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

### Example 8.3 Lorenz IVP — Julia pipeline VALIDATED (2026-03-01)

**Setup:** ẋ = f(x), x(0) = (1,0,0), σ=10, ρ=28, β=8/3, tail diagonal = n (rational).

**Conditioning fix:** Weighted scaling `diag(ν^k) · DF · diag(ν^{-k})` reduces cond from
10^254 (unweighted, ν=0.15) to ~2.5e3. Float64 inverse now gives ‖I-A_w·DF_w‖₁ ≈ 7.6e-14.

**N sweep results:**
| N | Status | Z₁ | r₋ | Matrix size |
|---|--------|------|----|-------------|
| 20 | ✗ | 0.42 | — | 63×63 |
| 25 | ✓ | 0.34 | 5.6e-3 | 78×78 |
| 30 | ✓ | 0.29 | 6.2e-4 | 93×93 |

**Chosen: N=30, ν=3/20.** Validated with interval arithmetic:
- Y₀ ≤ 4.4e-4, Z₀ ≤ 3.7e-14, Z₁ ≤ 0.29, Z₂ ≤ 4.71
- r₋ ≈ 6.2e-4 (proven ∃ true solution within ‖ã-ā‖ ≤ r₋ for t ∈ (-0.15, 0.15))

**Lean export:** `Numbers.lean` (736 lines) with sparse block-column format:
- ā: exact ℚ (BigInt Taylor recursion), 3 components × 31 modes = 93 entries
- A^(N): 9 blocks (3×3), sparse columns, rationalized Float64 (5681/8649 non-zero)
- DF^(N): 9 blocks, sparse columns, exact ℚ (2014/8649 non-zero)
- Bounds: simple ℚ rationals (Y₀=44/100000, Z₀=37/10^15, Z₁=30/100, Z₂=49/10)

**Scripts:** `julia/lorenz_ivp.jl` (full pipeline), `lorenz_ivp_sweep.jl` (N sweep),
`lorenz_ivp_export.jl` (Lean export)

---

### Example 8.3 Lorenz IVP — Lean formalization (2026-03-01, starting)

**API design decision**: IVP operator A† has tailDiag=n (unbounded) → can't be `SystemBlockDiagData`.
Added `BlockDiagOp` structure (finBlock+tailDiag only, no tailBound) to Base.lean with coercion.
Added `defectOfBlockDiagOp` to Concrete.lean (constructs defect from bounded A + unbounded B).

**Example83 files created:**
- `Algebra.lean`: `approxInverse` (SystemBlockDiagData, tailDiag=1/n, tailBound=1/31),
  `approxDeriv` (BlockDiagOp, tailDiag=n), `defect` (tailBound=0), `tailCancel`,
  `approxInverse_tailDiag_ne_zero`. Bridge lemmas for Numbers.lean ℚ data.
- `Certificate.lean`: Z₀ defect column infrastructure (`prodBlockCol`, `defectBlockCol`,
  `defectBlockCols`, `defectBlockCol_correct`), per-block norm bounds via
  `finWeightedMatrixNorm_le_via_cols`, ‖A‖ bound infrastructure. All with sorry for
  mechanical ℚ↔ℝ bridges and `finsum_bound` discharge.

**F_lorenz defined (2026-03-01):**
- `φ_lorenz`: Lorenz nonlinearity at `l1Weighted` level (ring multiplication = Cauchy product)
  - φ₀(a) = σ•(a₁ - a₀), φ₁(a) = ρ•a₀ - a₁ - a₀*a₂, φ₂(a) = -(β•a₂) + a₀*a₁
- `F_lorenz`: IVP zero-finding map `XL1 ν 3 → XL1 ν 3`
  - Mode 0: a_{j,0} - (x₀)_j; Mode k+1: (k+1)·a_{j,k+1} - φ_j(a)_k
- `F_lorenz_coeff_zero`, `F_lorenz_coeff_succ`: coefficient extraction via `simp only`
- Summability proof in F_lorenz is sorry'd (needs a ∈ l1Weighted + φ closure)

**Remaining sorry items:**
1. F_lorenz summability proof (membership in l1Weighted) — **BLOCKED: needs ω-weight space**
2. `defectBlockCol_correct` — mechanical ℚ↔ℝ bridge (Array.ofFn + push_cast)
3. `defect_blockEntryNorm_le` / `Z₀_finBlockNorm_le` — finsum_bound discharge
4. `A_blockEntryNorm_le` — finsum_bound discharge
5. fderiv F_lorenz — block-diagonal structure matching approxDeriv
6. Z₀ bridge: I - A∘DF = defect.toCLM (connects fderiv to defect)
7. `finite_block_injective_of_defect_norm_lt_one` — Neumann series (Concrete.lean, sorry)

### General API improvements (2026-03-01, session 2)

**Added to Base.lean:**
- `action_fin_eq_sum_mulVec`: bridge finite-mode action to `Matrix.mulVec`
- `blockFinite_mulVec_assoc`: block-matrix-vector associativity via `mulVec_mulVec` + `sum_comm`

**Added to Concrete.lean:**
- `defectOfBlockDiagOp_toCLM_eq` (Gap 1): CLM identity `I - A∘DF = defect.toCLM` for BlockDiagOp case
- `Z₀_norm_le_of_defect_plus_tail_error` (Gap 2): triangle combiner for Z₀ + Z₁
- `finite_block_injective_of_defect_norm_lt_one` (Gap 3): sorry, needs Neumann series

**Critical design discovery: IVP ω-weight space**
- F_lorenz does NOT map ℓ¹_ν → ℓ¹_ν (the `(n+1)*a_{n+1}` factor breaks summability for general a)
- Book (Section 8.1) uses Y = ℓ¹_ω where ω_n = ν^{n+1}/(n+1) — mode-dependent weight
- No single geometric weight μ^n works: F : ℓ¹_ν → ℓ¹_μ ok for μ < ν, but A : ℓ¹_μ → ℓ¹_ν fails
- Full project builds clean after this session's changes (Example77 unaffected)

### OmegaWeighted + F_lorenz retype (2026-03-01, session 3)

**Key architectural decision**: Do NOT generalize `lpWeighted`. Instead add a parallel `OmegaWeighted.lean`.

**New file: `OmegaWeighted.lean` (~250 lines)**
- `OmegaScaledReal ν n`: ℝ with norm `|x| * ν^{n+1}/(n+1)`
- Full `NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace` instances
- `l1Omega ν`, `YOmega ν L` abbreviations
- `omegaWeight_mul_index`: `(n+1) * ω_n = ν^{n+1}` (fundamental identity, Prop 8.1.5)
- `l1Omega.deriv_shift_mem`: `{(n+1)·a_{n+1}} ∈ ℓ¹_ω` when `a ∈ ℓ¹_ν`
- `l1Omega.geom_to_omega_mem`: `ℓ¹_ν ⊂ ℓ¹_ω` embedding
- `l1Omega.mem_of_finite_support`: finite-support membership

**Added to Concrete.lean:**
- `defect_of_composed_toCLM_eq`: composed CLM variant — `I - G_CLM = defect.toCLM` where G_CLM's coefficients match A·B directly. Avoids materializing the unbounded DF operator as a CLM.

**Modified Example83/Algebra.lean:**
- Retyped `F_lorenz : XL1 ν_val L → YOmega ν_val L` (was `→ XL1 ν_val L`)
- Coefficient lemmas updated to use `l1Omega.toSeq`/`l1Omega.mk_apply`
- Membership proof left as sorry (piecewise index alignment needed)

**Why not generalize lpWeighted:**
1. `ScaledReal` with function-valued type param (`w : ℕ → ℝ≥0`) breaks Lean defeq for `lp`
2. 14+ files would need `{ν : PosReal}` → `{w : ℕ → ℝ≥0}` signature changes
3. The omega space has NO ring structure — only Banach space needed
4. All existing files stay untouched — zero downstream breakage

**Continued: G_lorenz + theorem skeleton**
- `abar` defined via `abar_seq` with `dite` finite-support guard
- `G_lorenz = A ∘ F : XL1 → XL1` via `approxInverse.action(F_coeffs a)`
- `Dφ_lorenz` (linearization of Lorenz nonlinearity at ābar)
- `existsUnique` theorem skeleton compiles — Z₁=0 proven inline
- `Z₀_decomp` stated: ‖I - DG(ā)‖ ≤ ‖defect.toCLM‖ + ‖tail_error‖

**Continued: shiftDivN CLM + fderiv strategy**
- `shiftDivN_CLM : l1Weighted ν →L[ℝ] l1Weighted ν` — formal antiderivative as CLM (2 sorry: mem + norm)
- `differentiable_φ_lorenz_component` — proven via `fin_cases l <;> simp [φ_lorenz] <;> fun_prop`
- **Key insight**: G_lorenz tail = `id - shiftDivN_CLM ∘ φ`. Since shiftDivN is CLM (smooth) and φ is polynomial (`fun_prop` handles), G_lorenz differentiability follows from chain rule — no need for `lpWeighted.mk` smoothness bridge
- **PowerSeries connection**: `CauchyProduct.lean` has `toPowerSeries` bridge; Mathlib has `PowerSeries.derivative` = our IVP derivative. `shiftDivN` = formal antiderivative (not in Mathlib)

**6 sorry in Algebra.lean:** F_lorenz mem, G_lorenz mem, G_lorenz_tail, hasFDerivAt, Z₀_decomp, differentiable_G
**Next steps:** Redefine G_lorenz via shiftDivN_CLM → `fun_prop` differentiability → Certificate assembly

---

## Session 4: auto_poly_fderiv adaptation (2026-03-01)

**Goal:** Adapt Example 8.3 to use `auto_poly_fderiv` for Fréchet derivative computation.

### Completed
1. **`smul_proj_eq_leftMul_comp_proj`** (AutoPolyFDeriv.lean): Pi-level bridge for `auto_poly_fderiv` — converts `a • proj i → (leftMul a).comp (proj i)` for Banach algebra products on `Fin L → l1Weighted ν`.
2. **`shiftDivN_mem` + `shiftDivN_norm_le`** (OmegaWeighted.lean): Filled both sorry sites. Key: use `Summable.tsum_eq_zero_add` to split tsum, `summable_nat_add_iff` for shifted summability, `Summable.tsum_le_tsum` for pointwise bound.
3. **`fderiv_φ_lorenz_0/1/2`** (Algebra.lean): Per-component fderiv computed automatically via `auto_poly_fderiv`. Pattern: `show fderiv ℝ (fun a => <unfolded φ>) a = _; auto_poly_fderiv`.
4. **`Dφ_lorenz_eq_fderiv`** (Algebra.lean): Validates hand-written `Dφ_lorenz` matches tactic-computed fderiv at ābar.
5. **`fderiv_φ_diff_0/1/2`** (Algebra.lean): Fderiv differences for Z₂ — φ_lorenz is quadratic so fderiv difference is linear in (c-ā).
6. **`trunc_CLM`** (lpWeighted.lean): Truncation as CLM with ‖trunc a‖ ≤ ‖a‖.
7. **API improvements**: `ScaledReal.coe_abs`, `lpWeighted.mk_val_apply` — smooth coercion friction.

### Patterns discovered
- `by decide` not `by omega` for `Fin L` bounds when `L` is an abbrev
- `auto_poly_fderiv` on `Fin L → l1Weighted ν`: needs `proj_L` abbreviation to help inference
- `Summable.tsum_le_tsum` (not bare `tsum_le_tsum`) for ℝ-valued comparison
- `PosReal` coercion invisible to `positivity` — use explicit `ν.2.le` or `mul_nonneg`

### Remaining sorry (4 in Algebra.lean)
- F_lorenz mem, G_lorenz mem, G_lorenz_tail, hasFDerivAt/differentiable_G
- **Key blocker**: `lpWeighted.mk` is NOT a CLM — G_lorenz needs either redefinition or direct HasFDerivAt proof

### Full build: clean (8033 jobs)

---

## Session 4 (continued): Membership + Differentiability (2026-03-02)

**Goal:** Fill mechanical membership sorries + prove differentiability of G_lorenz.

### Filled sorries (6→1)
1. **F_lorenz ω-membership** — 1-liner via new API `l1Omega.mem_ivp_zero_finding`
2. **G_lorenz ℓ¹_ν-membership** — 15 lines via new API `mem_of_eventually_le_add_shift`
3. **G_lorenz_tail** — coefficient formula proven via `action_tail` + `field_simp`
4. **differentiable_G_lorenz** — proven via decomposition `G_lorenz = G_tail + G_fin_correction`
5. **hasFDerivAt_G_lorenz** — proven from differentiability

### G_lorenz differentiability architecture
```
G_lorenz = G_tail + G_fin_correction
G_tail(a)(l) = a l - shiftDivN_CLM(φ_lorenz a l)  [manifestly differentiable: CLM ∘ poly]
G_fin_correction(a)(l) = Σ_{k≤N} single_CLM k (correction_k(a))  [finitely supported]
```
- `differentiable_G_tail` — proven via `fun_prop`
- `differentiable_G_fin_correction` — uses `differentiable_mk_of_finSupp` (1 sorry: per-mode polynomial diff)
- `differentiable_G_lorenz` — follows from `Differentiable.add`

### New API (lpWeighted.lean)
- **`summable_weighted a`**: clean replacement for `(mem_iff _).mp a.2`
- **`summable_shifted_weighted b`**: `Σ|b_{n-1}|·ν^n` summable
- **`mem_of_eventually_le_add_shift`**: eventual domination → membership (uses `Summable.of_norm_bounded_eventually_nat`)
- **`toSeq_finset_sum`**: `toSeq (Σ g_i) n = Σ toSeq(g_i) n` — fundamental API layer
- **`single_CLM`**: embeds ℝ at index n as CLM
- **`single_toSeq`**: unified simp lemma `toSeq(single idx x) n = if n = idx then x else 0`
- **`differentiable_mk_of_finSupp`**: THE key API — differentiability of finitely-supported `lpWeighted.mk` functions. Decomposes as `Σ single_CLM k ∘ f_k`, uses `DifferentiableAt.fun_sum`.

### New API (OmegaWeighted.lean)
- **`l1Omega.mem_ivp_zero_finding`**: IVP zero-finding sequence `{c₀, (n+1)a_{n+1} - φ_n} ∈ ℓ¹_ω`

### Key insight
The `lpWeighted.mk` opacity was the systemic blocker. The fix: `differentiable_mk_of_finSupp` decomposes `mk f hf` into `Σ single_CLM k (f k)` and uses `DifferentiableAt.fun_sum`. This required:
1. `single_CLM` (embedding ℝ → l1Weighted at index k)
2. `toSeq_finset_sum` (pointwise evaluation of lp sums)
3. `single_toSeq` (unified simp lemma for `single` evaluation)

### Final sorry fill: `differentiable_G_fin_correction`
Per-mode polynomial differentiability proven via:
1. `toSeq_CLM` — coordinate evaluation as CLM, `@[fun_prop]` registered
2. `actionFinite` unfolded at finite modes → `Differentiable.fun_sum` of `const * F_coeffs` terms
3. Each `F_coeffs(a)_j_m` = `toSeq_CLM ∘ proj` (mode 0) or `const * toSeq_CLM ∘ proj - toSeq_CLM ∘ φ` (mode m+1)

### Algebra.lean: 1 sorry (`Z₀_le`) — all membership, differentiability, fderiv proven

### Z₀ architecture insight (discovered late in session)
The original `Z₀_eq_defect_norm` statement was **wrong**: `‖I - fderiv G ā‖ ≠ ‖defect.toCLM‖`.

Reason: `fderiv G_lorenz(ā)(h)` on tail mode n > N is `h_{l,n} - shiftDivN(Dφ(ā)(h))_n`, NOT `h_{l,n}`. So `(I - fderiv G ā)(h)` has nonzero tail = `shiftDivN(Dφ(ā)(h))`.

Correct decomposition: `‖I - fderiv G ā‖ ≤ ‖finite_defect‖ + ‖tail_Dφ_contribution‖`
where `tail_Dφ = shiftDivN_CLM ∘ Dφ_lorenz` on modes > N.

The Julia bounds (Z₀=3.7e-14, Z₁=0.3) use the ORIGINAL book decomposition (A=approxInverse, A†=approxDeriv), not our A=id setup. Architecture options for next session:
- **Option A**: Keep A=id, bound `‖I - fderiv G ā‖` via triangle (finite defect + ν·‖Dφ‖)
- **Option B**: Switch to A=approxInverse, use `Z₀_norm_le_of_defect_plus_tail_error` with Julia bounds directly. Requires `hdecomp` proof.

### Remaining: Z₀_le + Certificate.lean bounds

### Full build: clean (8033 jobs)

---

## BlockDiagSystem compile-time optimization (2026-03-02)

**Problem:** `RadiiPolynomial.SystemTaylorODE.BlockDiagSystem` took 203s to compile.

### Profiling results (before fixes)

| File | Compilation | Top costs |
|------|------------|-----------|
| Base.lean | ~20s | `.olean` serialization 7s, `simp` L445 643ms |
| Concrete.lean | ~8min | `StarRing` TC inference 19.9s, `simp` 9.6s, `.olean` 4.75s |
| Scalar.lean | ~2min | `StarRing` TC inference 15.6s, `simp` 4.7s, `.olean` 5.2s |

### Root cause: `StarRing` typeclass inference (dominant, ~35s total)

**Mechanism:** Mathlib's `@[simp] lemma norm_star : ‖x⋆‖ = ‖x‖` (in `Analysis/CStarAlgebra/Basic.lean`)
triggers on ANY `‖e‖` expression. To check if `e` matches `star x`, Lean synthesizes `Star (typeof e)` →
`StarAddMonoid` → `StarRing`. For types without star structure (`l1Weighted ν`, `ContinuousLinearMap`),
this search traverses the full class hierarchy before failing — 300-800ms per attempt.

`l1Weighted ν` has `NormedCommRing` but nobody registered the trivial `StarRing` instance that ℝ, ℚ, ℤ, ℕ
all have (via `starRingOfComm`). Mathlib deliberately doesn't make `starRingOfComm` a global instance
(would conflict with ℂ, quaternions), so each type must opt in.

**Fix (LpOneBanachAlgebra.lean):**
```lean
instance instStarRing : StarRing (l1Weighted ν) := starRingOfComm
instance instTrivialStar : TrivialStar (l1Weighted ν) := ⟨fun _ => rfl⟩
instance instNormedStarGroup : NormedStarGroup (l1Weighted ν) where
  norm_star_le _ := le_refl _
```
Mathematically correct (`star = id` for any commutative ℝ-algebra). Makes `StarRing` search succeed
instantly instead of failing slowly. Pi instance `StarRing (∀ i, f i)` then covers `XL1 ν L` automatically.

### Secondary fixes: slow `simp` calls

| Location | Before | Fix | After |
|----------|--------|-----|-------|
| Concrete L340 (`applyX_component_norm_le`) | 3 `simpa` ~3s | `simpa [let-binding]` → `exact` (definitional eq) | ~0ms |
| Scalar L228 (`norm_XL1_fin1`) | `simp` 1.94s | `rw [pi_norm_const]` | ~0ms |
| Scalar L77 (`norm_toCLM_le`) | `simpa` 1.1s | `rwa [finiteBlockMatrixNorm_eq]` | ~0ms |
| Scalar L320/355 | `simp` 1.1s | `rw [pi_norm_const]` | ~0ms |
| Base L444 (`comp_action_eq_action_comp_finite`) | `simp` 452ms | `simp only [...]` | ~200ms |
| Concrete L336 (`applyX_component_eq_finite_add_tail`) | `simp` ~300ms | `exact congr_fun (congr_fun ...)` | ~0ms |

### Result

| Metric | Before | After |
|--------|--------|-------|
| BlockDiagSystem total | **203s** | **141s** |
| StarRing inference | ~35s | ~0s (l1Weighted), ~1s residual (ContinuousLinearMap) |
| `.olean` serialization | ~17s | ~9s |

### Critical fix: `import Mathlib` → specific imports in NormHelpers.lean

NormHelpers.lean (74 lines) had `import Mathlib`, forcing the entire 7900-file Mathlib environment
to be loaded before compiling. Replaced with 4 specific imports:
```lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
```
This required adding explicit imports to lpWeighted.lean (which previously got `FDeriv.Linear` and
`FDeriv.Add` transitively through NormHelpers → Mathlib).

**Impact (clean build, mathlib cached):**

| Metric | Before | After |
|--------|--------|-------|
| Full chain wall time | **14:24** | **0:52** |
| NormHelpers | 120s | 8.9s |
| BlockDiagSystem (Scalar) | 107s | 5.8s |

### Lessons
1. **Never `import Mathlib`** — always use specific imports. Even for a 74-line file, loading all of Mathlib adds ~110s.
2. Any commutative ℝ-Banach algebra should register `StarRing` via `starRingOfComm` + `TrivialStar` + `NormedStarGroup` to avoid expensive failed typeclass searches from `norm_star`/`nnnorm_star` simp lemmas.
3. Replace `simpa [let-binding]` with `exact` when the let-binding is definitionally equal — saves ~1s per call.
4. Use `rw [pi_norm_const]` instead of `simp` for `‖fun _ => a‖ = ‖a‖` — saves ~2s.

---

## Session 5: Z₀/Z₁ architecture + Certificate pipeline (2026-03-02)

### Z₀/Z₁ Architecture Fix

**Problem:** A=id, A†=fderiv G ā gives Z₁=0 but Z₀ = ‖I - fderiv G ā‖ > 1 (tail ≈ ν·‖Dφ‖ ≈ 4.5).

**Fix:** Keep A=id, introduce `composedApprox : SystemBlockDiagData` as A† (block-diagonal A·DF product with tailDiag=1).
- Z₀ = ‖I - composedApprox.toCLM‖ = ‖defect.toCLM‖ ≈ 3.7e-14 (zero tail)
- Z₁ = ‖composedApprox.toCLM - fderiv G ā‖ ≈ 0.145 (tail shiftDivN∘Dφ)

### New API (general, reusable)

| File | API | Purpose |
|------|-----|---------|
| OmegaWeighted.lean | `l1_toSeq_shiftDivN` (@[simp]) | Bridge `l1Weighted.toSeq(shiftDivN b)` to `shiftDivN_seq` |
| OmegaWeighted.lean | `shiftDivN_tailTsum_le_div` | Tail of shiftDivN ≤ ν/(N+1)·‖b‖ (IVP Z₁ bound) |
| Concrete.lean | `norm_le_of_pi_component_bound` | Operator norm from per-component bounds |
| Base.lean | `differentiable_actionFinite`, `differentiable_action_fin` | Finite-mode action differentiability |
| LeanCertEval.lean | `blockDefectMatQ`, `blockDefectMatQ_correct` | Block-level ℚ↔ℝ defect bridge |
| LeanCertEval.lean | `colNormQ`, `finWeightedMatrixNormQ`, `finWeightedMatrixNorm_le_of_Q_le` | Single native_decide for matrix norm |

### Algebra.lean changes
- `composedApprox` + `composedApprox_defect_eq` (I - composedApprox = defect)
- `Z₀_le` proven via preassembled pipeline (defect.norm_toCLM_le)
- `Z₁_le` proven with delegated `htail_bound` hypothesis
- `existsUnique` updated: A†=composedApprox.toCLM, Z₁ as parameter
- `clm_apply` macro for CLM evaluation simp set
- `ν_q` abbreviation for ℚ weight
- Eliminated calc block in G_lorenz membership

### Certificate.lean progress
- `defectBlockCols` + `defectBlockCol_correct` — per-block column bridge (proven)
- `defect_blockEntryNorm_le` — 9 `native_decide` calls via `fin_cases l <;> fin_cases j` (proven)
- `Z₀_finBlockNorm_le` — sorry (mechanical chain)
- `A_blockEntryNorm_le` — unification issue after `fin_cases` (needs fix)

### Key discovery: `finsum_bound` generalization needed
Per-column `finsum_bound` (279 calls for L=3, N=30) times out. Solution: ℚ evaluator (`finWeightedMatrixNormQ`) + single `native_decide` per block. Future: extend `finsum_bound` tactic to recognize matrix/block norm goals and dispatch to ℚ evaluator automatically.

### Full build: clean (Certificate.lean has expected sorry warnings)

---

## Session 6: Y₀ bound PROVEN (2026-03-02, session 3)

### Goal
Prove `Y₀_le : ‖G_lorenz abar‖ ≤ Y₀_bound` via operator norm approach.

### New general API (reusable for any Chapter 8.2 IVP)

**CauchyProduct.lean:**
- `map_CauchyProduct`: ring hom distributes through Cauchy product
- `ratCast_CauchyProduct`: `↑(CauchyProduct f g n) = CauchyProduct (↑f) (↑g) n` for ℚ→ℝ

**WitnessSpec.lean:**
- `norm_toCLM_apply_le`: Y₀ pipeline — bounds `‖A.toCLM(v)‖` via per-component finite sums of `|A.action(toCoeff v) l n| * ν^n`. Combines `norm_toCLM_component_eq_Icc_sum` + `pi_norm_le_iff_of_nonneg`.

### Certificate.lean Y₀ proof chain
1. `abar_toSeq_eq` — abar sequence = raw ℚ getD for all modes
2. `φ_lorenz_Q` + `φ_lorenz_bridge` — ℚ mirror of φ_lorenz + bridge (uses `ratCast_CauchyProduct`)
3. `F_coeffs_Q` + `F_coeffs_bridge` — ℚ mirror of F_coeffs + bridge
4. `F_coeffs_abar_support` + `F_coeffs_abar_mem` — finite support → ℓ¹_ν membership
5. `F_abar : XL1 ν L` — embedding via `ofCoeff`
6. `G_lorenz_eq_toCLM_F_abar` — G(ā) = A.toCLM(F_abar) (sequence-level equality)
7. `Y₀_eval` + `Y₀_eval_correct` — per-term evaluator + correctness wrapper
8. **`Y₀_le`**: PROVEN via `norm_toCLM_apply_le` + `finsum_bound using Y₀_eval` (3 `native_decide`)

### Design principle validated
- Bounds follow directly from operator norm definitions for block-diagonal operators
- Per-term witnesses via `systemBlockDiagActionEval` (no manual ℚ reflection needed beyond F_coeffs bridge)
- `ratCast_CauchyProduct` removes the main friction (distributing cast through Cauchy products)

### Key lessons
- `finsum_bound` needs the bound to be an unfolded ℚ literal (`unfold Y₀_bound`), not `(Y₀_bound : ℝ)`
- After `fin_cases l`, the variable `l` is consumed — use `_` wildcard for evaluator/correctness references
- `toCoeff (ofCoeff c hmem) = c` by `@[simp] toCoeff_ofCoeff` — but sometimes needs explicit `congr`/`rfl`

### Current Example 8.3 bound status
| Bound | Status | Method |
|-------|--------|--------|
| Z₀ | ✅ PROVEN | `finmatrix_bound` (1 `native_decide`) |
| ‖A‖ | ✅ PROVEN | `norm_toCLM_le_of_Q` (1 `native_decide`) |
| Y₀ | ✅ PROVEN | `norm_toCLM_apply_le` + `finsum_bound` (3 `native_decide`) |
| Z₁ | ❌ PENDING | needs shiftDivN bound + Dφ norm bound |
| Z₂ | ❌ PENDING | needs bilinear fderiv difference bound |
| radii_neg | ❌ PENDING | needs r₀_val + `fast_bound` |

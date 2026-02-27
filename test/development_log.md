# Development Log

## Pattern: Subtype tsum → Finite sum via `tsum_subtype` + `tsum_eq_sum`

**Problem:** Converting `∑' (n : {n : ℕ // N < n}), f n` to `∑ n ∈ Finset.Icc (N+1) M, f n` when `f` is zero outside `[N+1, M]`. The manual approach uses `Finset.subtype`, `Finset.sum_map`, `Finset.sum_attach` — very verbose (~50 lines).

**Solution:** Two Mathlib lemmas compose cleanly:
1. `tsum_subtype`: `∑' (x : ↑s), f x = ∑' x, s.indicator f x`
2. `tsum_eq_sum`: `(∀ b ∉ s, f b = 0) → ∑' b, f b = ∑ b ∈ s, f b`

**Gotcha:** `rw [tsum_subtype]` fails because `{n // N < n}` doesn't syntactically match `↑(Set.Ioi N)` even though they're definitionally equal. Use `have h := tsum_subtype ...; rw [h]` instead.

**Template:**
```lean
-- Given: f zero outside [N+1, M], goal: ∑' (n : {n // N < n}), f n = ∑ n ∈ Icc (N+1) M, f n
have h1 : ∑' (n : {n // N < n}), f n = ∑' n, (Set.Ioi N).indicator f n :=
  tsum_subtype (Set.Ioi N) f
rw [h1, tsum_eq_sum (s := Finset.Icc (N + 1) M)]
· -- indicator = f on Icc: split_ifs, omega
· -- indicator = 0 outside Icc: split_ifs, use zero hypothesis
```

**Applied to:** `tail_tsum_eq_Icc_sum` in `Example_7_7.lean` (50 → 28 lines).

**Potential further targets:** `I_sub_comp_tail_tsum_zero`, `tail_cauchy_bound` in the same file.

---

## Refactor: Extract BlockDiag to separate file

**What:** Extracted `BlockDiag` namespace (structure + action + toCLM + injective_of_parts + norm lemmas) from `OperatorNorm.lean` into new `BlockDiag.lean`.

**Why:** Clean separation of concerns. `OperatorNorm.lean` keeps finite-dimensional weighted norms and Proposition 7.3.14. `BlockDiag.lean` is the block-diagonal operator interface.

**New simp lemmas added:**
- `action_finite`: When `n ≤ N`, action = matrix-vector product
- `action_tail`: When `N < n`, action = scalar * entry
- `action_fin`: When index is `Fin (N+1)`, action = matrix-vector product (auto-coercion)

**Gotcha:** These simp lemmas work for abstract `A : BlockDiagOp`, but NOT for struct literals like `{ finBlock := ..., tailDiag := ..., ... }.action`. In `Example_7_7.lean`, `approxInverse`/`approxDeriv` unfold to struct literals, so those proofs still use the manual `simp only [approxInverse, BlockDiag.BlockDiagOp.action, ...]` pattern.

**Files changed:**
- NEW: `RadiiPolynomial/TaylorODE/BlockDiag.lean`
- `RadiiPolynomial/TaylorODE/OperatorNorm.lean` — removed ~320 lines, now imports BlockDiag
- Phase 2 (done): Generalized tail to mode-dependent diagonal (see below)

---

## Pattern: Eliminating calc blocks with `.trans` + `gcongr`

**Problem:** Verbose calc blocks for chained inequalities like `‖A∘B‖ ≤ ‖A‖·‖B‖ ≤ max(…)·(2·r) = Z₂·r`. Each step needs `mul_le_mul_of_nonneg_left/right` + nonnegativity proof.

**Solution:** Two Mathlib tactics replace most calc boilerplate:
- `gcongr`: Automatically decomposes `a*b ≤ c*d` into `a ≤ c` + `b ≤ d`, handles nonnegativity
- `.trans` / `.trans_eq`: Chain inequalities without calc syntax

**Template (inequality then ring rearrangement):**
```lean
-- Old (5 lines):
calc a * b ≤ a * c := by apply mul_le_mul_of_nonneg_left h (by positivity)
  _ = c * a := by ring

-- New (1 line):
exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)
```

**Template (submultiplicativity chain):**
```lean
-- Old (19-line calc for Z₂_bound_valid)
-- New (6 lines):
rw [Z₂_bound_eq_two_mul_max]
have h_B : ‖fderiv...‖ ≤ 2 * r := (norm_fderiv_F_diff_le ...).trans (by gcongr)
exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
  ((mul_le_mul (approxInverse_norm_le ...) h_B (by positivity) (by positivity)).trans_eq (by ring))
```

**Key insight:** `gcongr` can't always figure out the right intermediate expression for `.trans`. When it fails, extract intermediate bounds with `have` then chain manually.

**Applied to Example_7_7.lean:**
- `norm_fderiv_F_diff_le`: 5-line calc → 2 lines (no calc)
- `Y₀_bound_valid` inner calc: 7 lines → 3 lines
- `tail_cauchy_bound`: 4-line calc → 1 line
- `Z₀_bound_valid`: 7-line calc → 4 lines (no calc)
- `Z₁_bound_valid`: 5-line calc → 2 lines (no calc)
- `Z₂_bound_valid`: 19-line calc → 6 lines (no calc)

---

## Refactor: Generalize BlockDiagOp tail (scalar → mode-dependent diagonal)

**What:** Changed `tailScalar : ℝ` to `tailDiag : ℕ → ℝ` + `tailBound : ℝ` + `tailBound_spec`.

**Why:** For IVP examples (book Sections 8.1, 8.2), the tail diagonal varies with mode index:
- Example 7.7 (algebraic x²-λ=0): constant `fun _ => 1/(2ā₀)` — unchanged
- Section 8.1 (scalar IVP ẋ=f(x)): `fun n => 1/n` — mode-dependent
- Section 8.2 (systems): same `ℕ → ℝ`, L independent copies on `(ℓ¹_ν)^L`

**Structure (before → after):**
```lean
-- Before:
structure BlockDiagOp (ν : PosReal) (N : ℕ) where
  finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  tailScalar : ℝ

-- After:
structure BlockDiagOp (ν : PosReal) (N : ℕ) where
  finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  tailDiag : ℕ → ℝ
  tailBound : ℝ
  tailBound_spec : ∀ n, N < n → |tailDiag n| ≤ tailBound
```

**Design decision:** `tailBound` is structural (inside the structure), not hypothesis-based. This keeps `toCLM` and all downstream code clean — no extra `C hC` arguments needed.

**Key lemma changes:**
- `tailScalar_norm_eq` (equality) → `tailDiag_norm_bound` (inequality using `Summable.tsum_le_tsum`)
- `action_tail` RHS: `A.tailScalar * a n` → `A.tailDiag n * a n`
- `norm_toCLM_le`: `max(K, |tailScalar|)` → `max(K, tailBound)`
- `injective_of_parts`: `tailScalar ≠ 0` → `∀ n, N < n → tailDiag n ≠ 0`

**Example 7.7 adaptation (constant tail):**
```lean
def approxInverse ... : BlockDiagOp ν N where
  finBlock := A_fin
  tailDiag := fun _ => 1 / (2 * sol.aBar_fin 0)
  tailBound := |1 / (2 * sol.aBar_fin 0)|
  tailBound_spec := fun _ _ => le_refl _
```

**Files changed:**
- `RadiiPolynomial/TaylorODE/BlockDiag.lean` — structure + all lemmas updated
- `RadiiPolynomial/TaylorODE/OperatorNorm.lean` — Prop 7.3.14 updated
- `RadiiPolynomial/TaylorODE/Example_7_7.lean` — struct definitions + ~10 lemmas adapted
- `RadiiPolynomial/TaylorODE/Example_7_7_LeanCert_Clean.lean` — builds unchanged (inherits from Example_7_7)

---

## Update (Direct branch, 2026-02-25)

Detailed intermediate refactor notes were pruned in favor of the current-state
summary below.

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
- Added `Rat.cast` support to LeanCert reifier (ToExpr.lean) for ℚ→ℝ cast handling
- `arrayColNormIccSum` is the bridge layer between `matrixColNorm` and `finsum_bound`
- CLM-level lifting uses BlockDiagSystem structural lemmas
- `approxInverse_injective` removed from Algebra.lean — certificate calls general API directly

### Scalar-specific APIs for later generalization (2026-02-26)

APIs currently L=1 only, need general-L for Section 8.2:
- `norm_toScalarCLM_le` → need per-component `norm_toCLM_le`
- `existsUnique_of_scalar_bounds` → system version
- `injective_toScalarCLM_of_finBlock_mul_close_to_one` → per-component Neumann
- `toScalarCLM_support`, `norm_toScalarCLM_action_eq_Icc_sum` → per-component
- `norm_toScalarCLM_le_via_colNorm` (LeanCertEval) → system version with block norms
- `Z₀_le_via_colNorm` (LeanCertEval) → already uses general `Z₀_le_of_tailCancel`

### Reusable infrastructure extracted

- In `OperatorNorm.lean`:
  `BlockDiag.BlockDiagOp.injective_of_finBlock_mul_close_to_one`.
- This packages the pattern:
  `‖1 - A.finBlock * B‖_{1,ν} < 1` + nonzero tail diagonal
  ⇒ `Function.Injective A.toCLM`.

### Cleanup completed

- Removed stale commented refactor block from `Example_7_7_LeanCert.lean`.
- Updated file docstrings to describe the active direct pipeline.
- Pruned `TaylorODE_Direct/Example_7_7.lean` to core structural content:
  - kept definitions + structural lemmas used by `Example_7_7_LeanCert.lean`
    and `Example_7_7_Analytic.lean`
  - removed legacy symbolic-reduction theorem assembly (`*_bound_valid`,
    injectivity-from-radii, old main theorem) now preserved in the copied
    `RadiiPolynomial/TaylorODE` branch.

### Additional cleanup (Direct branch, 2026-02-25)

- Deprecated-and-removed the remaining legacy scalar bound layer from
  `TaylorODE_Direct/Example_7_7.lean`:
  - `Y₀_bound`, `Z₀_bound`, `Z₁_bound`, `Z₂_bound`
  - `radiiPoly_7_7`
  - `Z₂_bound_eq_two_mul_max`
- Removed now-unused import `RadiiPolynomial.RadiiPolyGeneral` from the Direct file.
- Kept only structural CLM/operator lemmas in the Direct file; the old
  bound-formula path remains in `RadiiPolynomial/TaylorODE`.

### Canonical norm-level replacement (Direct branch, 2026-02-25)

- Added canonical norm definitions in `TaylorODE_Direct/Example_7_7.lean`:
  - `Y₀_norm := ‖A·F(ā)‖`
  - `Z₀_norm := ‖I - A·A†‖`
  - `Z₁_norm := ‖A·(A† - DF(ā))‖`
  - `Z₂_norm c := ‖A·(DF(c) - DF(ā))‖`
- Updated `TaylorODE_Direct/Example_7_7_LeanCert.lean` so
  `Y₀_norm_le`, `Z₀_norm_le`, `Z₁_norm_le`, `Z₂_norm_le`
  are stated directly against these canonical definitions.

### Structural extraction: `I - A ∘ B` lemmas (Direct branch, 2026-02-25)

- Moved generic finite/tail decomposition lemmas from example-specific proofs
  into `TaylorODE_Direct/BlockDiag.lean`:
  - `BlockDiagOp.I_sub_comp_action_finite_eq`
  - `BlockDiagOp.I_sub_comp_action_tail_eq_zero_of_tail_mul_eq_one`
  - `BlockDiagOp.I_sub_comp_finite_toSeq_eq`
- Updated `TaylorODE_Direct/Example_7_7.lean` to use these generic lemmas and
  removed the local helper `approxDeriv_toSeq_eq_action`.

### API extraction: direct theorem wrappers (Direct branch, 2026-02-25)

- Added reusable theorem-level API in `TaylorODE_Direct/Example_7_7.lean`:
  - `approxInverse_injective_of_Z₀_lt_one`
  - `existsUnique_of_direct_bounds`
  - `existsUnique_of_direct_bounds_of_Z₀_lt_one`
- These wrappers consume canonical norm bounds (`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`)
  and directly instantiate `general_radii_polynomial_theorem`.
- Updated `TaylorODE_Direct/Example_7_7_LeanCert.lean`:
  - `A_op_injective` now uses `approxInverse_injective_of_Z₀_lt_one`
  - `main_theorem` now instantiates `existsUnique_of_direct_bounds` instead of
    assembling `general_radii_polynomial_theorem` inline.

### New module scaffold: `SystemTaylorODE` (2026-02-25)

- Started a new folder for Section 8.2-style systems:
  - `RadiiPolynomial/SystemTaylorODE/Core.lean`
  - `RadiiPolynomial/SystemTaylorODE/BlockDiagSystem.lean`
  - umbrella import `RadiiPolynomial/SystemTaylorODE.lean`
- `Core.lean` introduces systems space
  `Space ν L := Fin L → l1Weighted ν` and canonical norm-level quantities:
  - `Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`
- Added theorem wrappers specialized to `(ℓ¹_ν)^L`:
  - `existsUnique_of_direct_bounds`
  - `existsUnique_of_direct_bounds_constZ₂`
- `BlockDiagSystem.lean` lifts scalar block-diagonal operators componentwise:
  - `ComponentwiseBlockDiagOp.toCLM`
  - `injective_of_components`
  - `injective_of_finBlock_mul_close_to_one` (componentwise version)
- Build check passed for:
  - `RadiiPolynomial.SystemTaylorODE.Core`
  - `RadiiPolynomial.SystemTaylorODE.BlockDiagSystem`
  - `RadiiPolynomial.SystemTaylorODE`

### Reference alignment (pages 185-201) + API follow-up (2026-02-25)

- Reviewed reference pages 185-201 (`183-220.pdf`, extracted with `pdftotext`):
  - 8.1/8.2 setup uses distinct spaces `X = (ℓ¹_ν)^L`, `Y = (ℓ¹_ν')^L` with `ν' < ν`.
  - System map is coefficient-level `F : X → Y` (Eq. 8.15), then truncated finite problem
    via `π_N`, `π_{N,∞}` and `ι_N` (Eq. 8.16-8.17).
  - Conceptual block structure for `DF(ā)`, `A†`, `A` in finite+tail decomposition
    (pages 197-199; Eq. 8.19-8.21).
  - System bounds `Y₀, Z₀, Z₁, Z₂` are componentwise/max-aggregated (Theorem 8.2.2,
    Eq. 8.22-8.24).
- Updated `SystemTaylorODE/Core.lean` to match this:
  - explicit aliases `X ν L` and `Y ν' L`;
  - canonical norm quantities and theorem wrappers now use `f : X -> Y`,
    `A : Y -> X`, `A† : X -> Y`.
- Added `SystemTaylorODE/Setup82.lean` with foundational 8.2 bookkeeping:
  - `piComponent`;
  - truncation/projections `piNScalar`, `piN`, `piNInf`;
  - finite/tail sets `XN`, `XNInf`, `YN`, `YNInf`;
  - coefficient-level operators `shiftCoeff` (Eq. 8.25) and `lambdaNCoeff` (Eq. 8.26).
- Updated umbrella import `RadiiPolynomial/SystemTaylorODE.lean` to include `Setup82`.
- Build check passed for `RadiiPolynomial.SystemTaylorODE`.

### SystemTaylorODE concrete sequence backend (2026-02-25)

- Added self-contained concrete infrastructure under `RadiiPolynomial/SystemTaylorODE`:
  - `ScaledReal.lean`: `SystemTaylorODE.PosReal`, `ScaledReal ν n`, weighted fiber norm.
  - `CauchyProduct.lean`: sequence convolution API (`CauchyProduct`) + algebraic lemmas.
  - `lpWeighted.lean`: `lpWeighted`, `l1Weighted`, norm/membership bridge lemmas,
    finite weighted matrix norms, array-column bridge formulas, truncation API.
- Wired umbrella/module imports:
  - `SystemTaylorODE.lean` now imports the concrete infrastructure before `Core/Setup82/BlockDiagSystem`.
  - `Core.lean` now imports `SystemTaylorODE.ScaledReal`, so `PosReal` is concrete (not auto-implicit).
- Added concrete `SeqModel` instance in `Setup82.lean`:
  - `instSeqModel_l1Weighted : SeqModel (fun ν => ↥(l1Weighted ν))`
  - implemented by `lpWeighted.toSeq`, `l1Weighted.trunc`, and coefficient lemmas.
- Build status:
  - `lake build RadiiPolynomial.SystemTaylorODE` passes.

### Chapter 8: key findings and key goals (working summary)

Key findings:
- The Chapter 8 system setup is not a direct reuse of scalar `X = Y`; it needs
  `X = (ℓ¹_ν)^L` and `Y = (ℓ¹_ν')^L` with `ν' < ν`.
- The core 8.2 pipeline is structurally finite+tail:
  `F` in coefficient form, truncation via `π_N/π_{N,∞}`, finite problem `F^(N)`,
  then block-structured `A†` and `A`.
- Theorem 8.2.2 bounds are aggregated over component pairs `(l,j)` using max/sums,
  not a single scalar-column pattern.
- Existing `TaylorODE_Direct` infrastructure is reusable at the operator-norm level,
  but system-level bookkeeping (`ι_N`, truncation spaces, pair-indexed bounds) must be added.

Key goals:
- Implement the finite-dimensional bridge of Eq. 8.16-8.17 in `SystemTaylorODE`
  (`ι_N`, `F^(N)`, and compatibility lemmas).
- Add system operators `A†` and `A` as finite+tail constructions (Eq. 8.19-8.21),
  with CLM wrappers and injectivity criteria.
- Formalize system-level `Y₀/Z₀/Z₁/Z₂` bound APIs in the Theorem 8.2.2 shape
  (pair-indexed constants + global aggregations).
- Reuse LeanCert evaluators for finite sums/matrix terms in system form and
  connect them to direct norm statements (no symbolic-reduction dependency).

### SystemTaylorODE self-containment refactor (2026-02-25)

- Removed direct imports from sibling folder `TaylorODE_Direct` in
  `SystemTaylorODE` modules.
- Refactored `SystemTaylorODE/Core.lean` to be abstract over a sequence-space
  family `Seq : PosReal → Type*` with Banach-space assumptions.
- Refactored `SystemTaylorODE/Setup82.lean` to use an internal interface
  `SeqModel` (`coeff`, `trunc`, structural coefficient lemmas), avoiding
  concrete dependency on `l1Weighted`.
- Refactored `SystemTaylorODE/BlockDiagSystem.lean` to an abstract
  componentwise-CLM lifting API:
  - `ComponentwiseBlockDiagOp.toCLM`
  - `injective_of_components`
  - `injective_of_component_certificates`
- Build check passed for `RadiiPolynomial.SystemTaylorODE`.

### SystemTaylorODE block-operator follow-up (2026-02-25)

- Generalized system block structure in `SystemTaylorODE/BlockDiagSystem.lean`:
  - added coupled block lifting `ComponentwiseMatrixOp.toCLM` for `L×L` CLM blocks.
  - added finite block aggregation API:
    `blockEntryNorm`, `blockRowNorm`, `finiteBlockMatrixNorm = max_l Σ_j ‖A_{l,j}‖`.
- Added concrete 8.2-style coefficient data structure:
  - `SystemBlockDiagData` with:
    - coupled finite block (`finBlock : Fin L → Fin L → Matrix ...`)
    - componentwise tail diagonal (`tailDiag : Fin L → ℕ → ℝ`)
    - uniform tail bound certificate (`tailBound_spec`).
  - coefficient-level decomposition:
    - `actionFinite` (finite modes)
    - `actionTail` (tail diagonal)
    - `action = actionFinite + actionTail` (Eq. 8.21 shape).
- Added concrete `(ℓ¹_ν)^L` lift:
  - `toCoeff`, `ofCoeff`, membership transfer lemmas.
  - `SystemBlockDiagData.applyX : (ℓ¹_ν)^L → (ℓ¹_ν)^L`.
  - linearity lemmas `applyX_add`, `applyX_smul`.
  - `SystemBlockDiagData.toLinearMap`.
- Build checks passed:
  - `lake build RadiiPolynomial.SystemTaylorODE.BlockDiagSystem`
  - `lake build RadiiPolynomial.SystemTaylorODE`.

### Direct certificate witness integration (2026-02-25)

- In `RadiiPolynomial/TaylorODE_Direct/DirectRadiiCertificate.lean`,
  added a dedicated `WitnessBridge` section connecting ODE-specific direct norms
  to `canonicalWitness` term sums:
  - `canonicalWitness_Y₀_sum_eq`, `canonicalWitness_Z₀_sum_eq`,
    `canonicalWitness_Z₁_sum_eq`, `canonicalWitness_Z₂_sum_eq`
  - `Y₀_norm_le_witness_sum`, `Z₀_norm_le_witness_sum`,
    `Z₁_norm_le_witness_sum`, `Z₂_norm_le_witness_sum`
- Added `main_theorem_via_witness`, proving existence/uniqueness through
  witness terms and witness sum APIs (instead of hard-coded scalar bounds).
- Kept `main_theorem` unchanged as the direct constant-bound path.
- Updated docstrings in the same file to reflect the witness-driven route.
- Checks passed:
  - `lake env lean RadiiPolynomial/TaylorODE_Direct/DirectRadiiCertificate.lean`
  - `lake build RadiiPolynomial.TaylorODE_Direct.DirectRadiiCertificate`

### New scalar-specific APIs for general-L generalization (2026-02-26)

New APIs added to `Scalar.lean` (L=1 only, need general-L for Section 8.2):
- `tailTsum_toScalarCLM_le` — tail action weighted bound: `∑' n ≥ N+1, ν^n |Ax_n| ≤ tailBound * ‖x‖`
- `finRangeSum_toScalarCLM_le` — finite action weighted bound: `∑ n ∈ range(N+1), ν^n |Ax_n| ≤ matrixColNorm * ‖x‖`
- `norm_toScalarCLM_le_max` — tight max bound for block-diagonal ℓ¹ operator norm (Exercise 2.7.2): `‖A‖ ≤ max(matrixColNorm, tailBound)`

New APIs added to `LeanCertEval.lean`:
- `norm_toScalarCLM_le_max_via_colNorm` — pipeline: column norm bounds + tail bound → `‖A‖ ≤ C` via max
- `of_point_interval` — wraps `fast_bound` for scalar ℚ-cast inequalities (e.g. `↑q ≤ b`)

New API added to `lpWeighted.lean`:
- `norm_eq_finRangeSum_add_tailTsum` — norm splitting: `‖x‖ = ∑ n < N+1 + ∑' n ≥ N+1`

These decompose the operator norm into finite+tail parts, then bound each separately.
The `norm_toScalarCLM_le_max` lemma replaces the looser additive bound `norm_toScalarCLM_le`
with a tight max-based bound matching Exercise 2.7.2 of the reference book.

**General-L versions needed for Section 8.2:** Each of these three Scalar.lean APIs needs
a per-component analogue operating on `(ℓ¹_ν)^L`, with system-level aggregation via max over components.

### Certificate sorry progress (2026-02-27)

**Completed (4/6):** `radii_neg`, `Z₀_le`, `A_injective`, `A_norm_le`

**A_norm_le design:**
- Uses `norm_toScalarCLM_le_max` (max bound) + `finWeightedMatrixNorm_le_via_cols` (column norms via `finsum_bound`) + `of_point_interval`/`fast_bound` (tail bound + final `2*C ≤ Z₂_bnd`)
- No `calc`, no `linarith` — all numerical steps via `fast_bound`/`finsum_bound`

**Y₀_le completed (2026-02-27):**
- `F_ā_support` — `CauchyProduct.zero_of_support`
- `AF_ā_support` — `toScalarCLM_support`
- `norm_eq_Icc_sum_of_support` → 5-term Icc sum
- `toScalarCLM_toSeq_eq_action` bridges each `toSeq(A(F(ā)))[n]` to `↑(scalarBlockDiagAction ...)`
- `finsum_bound using Y₀_eval` closes with witness evaluator

**Key lesson**: `finsum_bound` reifier can't handle complex Lean (antidiagonal, dite, match). Must bridge norm body to `↑(ℚ_function n)` form. Direct ℝ-only unfolding doesn't work.

**API additions (2026-02-27):**
- `F_toSeq` (Algebra.lean): `toSeq(F(a))[n] = CauchyProduct(toSeq a, toSeq a)[n] - paramSeq(λ₀)[n]`
- `of_point_interval` simplified to ℝ-general (no `{q : ℚ}` param)
- `toScalarCLM_toSeq_ite`: uniform ℝ per-coeff formula via `dite`
- `scalarBlockDiagAction` + `toScalarCLM_toSeq_eq_action` + `scalarBlockDiagActionEval/_correct`: norm-to-witness bridge pipeline
- `A_col_bridge` moved before Y₀ section (shared by Y₀ and Z₀)

**Z₁_le in progress (2026-02-27):**

3-layer architecture wired up:
1. **Scalar.lean**: `norm_comp_of_fin_kill` — general API: if inner op T kills finite modes, ‖A.comp T‖ ≤ tailBound·‖T‖. Proof via `opNorm_le_bound` + finite part = 0 + `tailTsum_toScalarCLM_le`.
2. **Algebra.lean**:
   - `approxDeriv_sub_fderiv_fin_kill` ✅ — shows (A†-DF)(h)[n]=0 for n≤N by matching `dfFin` lower-triangular sum with `2•leftMul` Cauchy product on finite modes.
   - `norm_approxDeriv_sub_fderiv_le` ❌ SORRY — needs ‖A†-DF‖ ≤ 2·∑|ā_m|ν^m. Requires porting `shiftedSeq`/`shiftedL1`/`tail_cauchy_bound` from DirectCore.lean (Young's inequality for shifted convolution).
3. **Algebra.lean**: `Z₁_le_via_eval` — chains `norm_comp_of_fin_kill` + equation-specific bounds. (Moved from LeanCertEval.lean — LeanCertEval must stay general, no Example77 deps.)
4. **Certificate.lean**: `Z₁_le` — calls `Z₁_le_via_eval sol A_mat lam0 Z₁_bnd (of_point_interval (by unfold ...; fast_bound))`.

**Design rule**: LeanCertEval.lean = general evaluators only. Equation-specific pipelines go in Algebra.lean.

**Remaining**: Fill `norm_approxDeriv_sub_fderiv_le` sorry in Algebra.lean (Young bound for ‖A†-DF‖).
Approach: `opNorm_le_bound` → finite part=0 (via `fin_kill`) → tail = shifted convolution → define `shiftedSeq`/`shiftedL1` → Young/submultiplicativity bound. Port from DirectCore.lean:471-543.

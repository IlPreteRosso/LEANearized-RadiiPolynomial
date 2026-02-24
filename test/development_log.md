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

**Gotcha:** These simp lemmas work for abstract `A : BlockDiagOp`, but NOT for struct literals like `{ finBlock := ..., tailScalar := ... }.action`. In `Example_7_7.lean`, `approxInverse`/`approxDeriv` unfold to struct literals, so those proofs still use the manual `simp only [approxInverse, BlockDiag.BlockDiagOp.action, ...]` pattern.

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

import RadiiPolynomial.TaylorODE.OperatorNorm
import Mathlib.Tactic.Bound

variable {ν : PosReal}

-- ============================================================
-- PATTERN 1: Z₂-style chain: ‖A∘B‖ ≤ K·(2·r) = 2·K·r
-- ============================================================

-- gcongr needs 0 ≤ K. Derive it from ‖A‖ ≤ K + norm_nonneg.
-- This is always available in our proofs since K = max(norm, bound) ≥ 0.

-- Working version with gcongr
example (A B : l1Weighted ν →L[ℝ] l1Weighted ν) (K r : ℝ)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ 2 * r) :
    ‖A.comp B‖ ≤ 2 * K * r := by
  have hK : 0 ≤ K := le_trans (norm_nonneg A) hA
  have : ‖A‖ * ‖B‖ ≤ K * (2 * r) := by gcongr
  linarith [ContinuousLinearMap.opNorm_comp_le A B]

-- Working one-liner (what we already use)
example (A B : l1Weighted ν →L[ℝ] l1Weighted ν) (K r : ℝ)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ 2 * r) :
    ‖A.comp B‖ ≤ 2 * K * r :=
  (ContinuousLinearMap.opNorm_comp_le A B).trans
    ((mul_le_mul hA hB (norm_nonneg _) (le_trans (norm_nonneg A) hA)).trans_eq (by ring))

-- ============================================================
-- PATTERN 2: bound with @[bound] tagged submultiplicativity
-- ============================================================

@[bound]
lemma clm_comp_norm_le' (A B : l1Weighted ν →L[ℝ] l1Weighted ν) :
    ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B

-- bound can't chain submult + product monotonicity in one shot.
-- It needs the submult step done first:
example (A B : l1Weighted ν →L[ℝ] l1Weighted ν) (K₁ K₂ r : ℝ)
    (hK₁ : 0 ≤ K₁) (hA : ‖A‖ ≤ max K₁ K₂) (hB : ‖B‖ ≤ 2 * r) (hr : 0 ≤ r) :
    ‖A.comp B‖ ≤ max K₁ K₂ * (2 * r) := by
  have := clm_comp_norm_le' A B  -- ‖A∘B‖ ≤ ‖A‖*‖B‖
  have : ‖A‖ * ‖B‖ ≤ max K₁ K₂ * (2 * r) := by bound
  linarith

-- ============================================================
-- PATTERN 3: K*fin + C*tail ≤ max(K,C)*(fin+tail)
-- ============================================================

-- This is the toCLM / Prop 7.3.14 pattern
example (K C fin_norm tail_norm fin_part tail_part : ℝ)
    (hfin_nn : 0 ≤ fin_norm) (htail_nn : 0 ≤ tail_norm)
    (hfin : fin_part ≤ K * fin_norm) (htail : tail_part ≤ C * tail_norm) :
    fin_part + tail_part ≤ max K C * (fin_norm + tail_norm) := by
  have h1 : K * fin_norm ≤ max K C * fin_norm := by gcongr; exact le_max_left _ _
  have h2 : C * tail_norm ≤ max K C * tail_norm := by gcongr; exact le_max_right _ _
  nlinarith

-- ============================================================
-- PATTERN 4: What a custom "norm_bound" tactic would look like
-- ============================================================

-- Rather than a new tactic, a macro that expands to:
--   have hK := ... ; have := opNorm_comp_le ...; gcongr/linarith
-- This is what our current Z₂_bound_valid already does, just spelled out.

-- The real question: can we do BETTER than our current code?
-- Current Z₂_bound_valid (6 lines):
--   rw [Z₂_bound_eq_two_mul_max]
--   have h_B : ‖...‖ ≤ 2 * r := (norm_fderiv_F_diff_le ...).trans (by gcongr)
--   exact (opNorm_comp_le _ _).trans
--     ((mul_le_mul (approxInverse_norm_le ...) h_B (by positivity) (by positivity)).trans_eq (by ring))

-- Hypothetical with full automation (3 lines):
--   rw [Z₂_bound_eq_two_mul_max]
--   have h_B : ‖...‖ ≤ 2 * r := (norm_fderiv_F_diff_le ...).trans (by gcongr)
--   norm_bound [approxInverse_norm_le, h_B]  -- applies submult + gcongr + ring

-- So the gain is ~1 line per chain. Probably not worth a custom tactic.
-- The `have + .trans + gcongr` pattern is already quite clean.

-- ============================================================
-- VERDICT
-- ============================================================
-- 1. `gcongr` is the best tool for monotone product steps.
--    It needs 0 ≤ K in context, derivable from `norm_nonneg` + transitivity.
-- 2. `bound` works when positivity can close nonnegativity
--    (max, abs, norms). @[bound] tagging helps with submultiplicativity.
-- 3. `linarith`/`nlinarith` handles final additive/ring cleanup.
-- 4. A custom tactic would save ~1 line per chain — not worth the maintenance.
-- 5. Current pattern (have + .trans + gcongr/mul_le_mul + ring) is near-optimal.

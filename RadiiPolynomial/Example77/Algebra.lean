import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Scalar

/-!
# Example 7.7 — Algebraic Infrastructure

Problem-specific algebra for the parameterized equilibrium `x² - λ = 0`.
Uses the `SystemTaylorODE/BlockDiagSystem` API exclusively (no `TaylorODE_Direct` dependency).

## Contents

1. **Fréchet derivative**: `leftMul`, `sq`, `F_sub_const`, and their derivatives
2. **Problem data**: `paramSeq`, `ApproxSolution`, `F`, `F_toSeq`
3. **Operator construction**: `approxDeriv`, `approxInverse` as `ScalarBlockDiagData`
4. **Z₁ infrastructure**: `shiftedSeq`/`shiftedL1` (shifted coefficient sequence),
   `approxDeriv_finBlock_eq_cauchy` (Cauchy bridge for fin block),
   `approxDeriv_sub_fderiv_fin_kill` (fin modes vanish via `toScalarCLM_toSeq_fin_eq_cauchy`),
   `approxDeriv_sub_fderiv_tail_eq` (tail equals `-2•leftMul(shiftedL1)`),
   `Z₁_le_via_eval` (chains `Z₁_le_of_fin_kill_tail_dom`)
5. **Z₂ and main theorem**: structural reductions to evaluable forms
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap SystemTaylorODE

noncomputable section

variable {ν : PosReal}

/-! ## 1. Fréchet Derivative for F(a) = a*a - c -/

namespace Example77

/-! ### Left multiplication as CLM -/

def leftMul (a : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := fun h => a * h
      map_add' := fun h₁ h₂ => mul_add a h₁ h₂
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, ← smul_eq_mul, ← smul_eq_mul]
        exact (smul_comm c a h).symm }
    ‖a‖
    (fun h => norm_mul_le a h)

lemma norm_leftMul_le (a : l1Weighted ν) : ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (fun h => norm_mul_le a h)

@[simp]
lemma leftMul_apply (a h : l1Weighted ν) : leftMul a h = a * h := rfl

lemma leftMul_smul (c : ℝ) (a : l1Weighted ν) :
    leftMul (c • a) = c • leftMul a := by
  ext1 h; simp only [leftMul_apply, coe_smul', Pi.smul_apply, ← smul_eq_mul]
  exact smul_mul_assoc c a h

lemma leftMul_add (a b : l1Weighted ν) :
    leftMul (a + b) = leftMul a + leftMul b := by
  ext1 h; simp only [leftMul_apply, add_apply]; exact add_mul a b h

lemma leftMul_sub (a b : l1Weighted ν) :
    leftMul (a - b) = leftMul a - leftMul b := by
  rw [sub_eq_add_neg, leftMul_add, ← neg_one_smul ℝ b, leftMul_smul]
  simp only [neg_one_smul]; abel

/-! ### Squaring map and F = sq - c -/

def sq (a : l1Weighted ν) : l1Weighted ν := a * a

def F_sub_const (c : l1Weighted ν) (a : l1Weighted ν) : l1Weighted ν := sq a - c

/-! ### Fréchet derivative -/

private lemma sq_expansion_comm (a h : l1Weighted ν) :
    sq (a + h) - sq a - (2 : ℝ) • leftMul a h = sq h := by
  simp only [sq, leftMul_apply, two_smul]; ring

private lemma sq_remainder_norm (a h : l1Weighted ν) :
    ‖sq (a + h) - sq a - (2 : ℝ) • leftMul a h‖ ≤ ‖h‖ ^ 2 := by
  rw [sq_expansion_comm]; exact (norm_mul_le h h).trans_eq (by ring)

theorem hasFDerivAt_sq (a : l1Weighted ν) :
    HasFDerivAt sq ((2 : ℝ) • leftMul a) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : l1Weighted ν) hε] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  exact ((sq_remainder_norm a h).trans_eq (by ring)).trans
    (mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg h))

theorem differentiable_sq : Differentiable ℝ (sq : l1Weighted ν → l1Weighted ν) :=
  fun a => (hasFDerivAt_sq a).differentiableAt

theorem fderiv_sq (a : l1Weighted ν) :
    fderiv ℝ sq a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_sq a).fderiv

theorem hasFDerivAt_F_sub_const (c a : l1Weighted ν) :
    HasFDerivAt (F_sub_const c) ((2 : ℝ) • leftMul a) a :=
  (hasFDerivAt_sq a).sub_const c

theorem differentiable_F_sub_const (c : l1Weighted ν) :
    Differentiable ℝ (F_sub_const c) :=
  fun a => (hasFDerivAt_F_sub_const c a).differentiableAt

theorem fderiv_F_sub_const (c a : l1Weighted ν) :
    fderiv ℝ (F_sub_const c) a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_F_sub_const c a).fderiv

/-- DF(c) - DF(ā) = 2 • leftMul(c - ā). Used for Z₂. -/
lemma fderiv_F_diff_eq (c_seq : l1Weighted ν) (a b : l1Weighted ν) :
    fderiv ℝ (F_sub_const c_seq) a - fderiv ℝ (F_sub_const c_seq) b =
    (2 : ℝ) • leftMul (a - b) := by
  rw [fderiv_F_sub_const, fderiv_F_sub_const, ← smul_sub, leftMul_sub]

/-- ‖DF(c) - DF(ā)‖ ≤ 2 * ‖c - ā‖. Used for Z₂. -/
lemma norm_fderiv_F_diff_le (c_seq : l1Weighted ν) (a b : l1Weighted ν) :
    ‖fderiv ℝ (F_sub_const c_seq) a - fderiv ℝ (F_sub_const c_seq) b‖ ≤
    2 * ‖a - b‖ := by
  rw [fderiv_F_diff_eq, norm_smul, Real.norm_ofNat]
  gcongr; exact norm_leftMul_le _

/-! ## 2. Problem Data -/

/-- The constant sequence c = (lam0, 1, 0, 0, ...) encoding λ = lam0 + t. -/
def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with | 0 => lam0 | 1 => 1 | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : lpWeighted.Mem ν 1 (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

def c (lam0 : ℝ) : l1Weighted ν := lpWeighted.mk (paramSeq lam0) (paramSeq_mem lam0)

/-- The zero-finding map F(a) = a*a - c(lam0). -/
def F (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν := F_sub_const (c lam0) a

lemma F_eq (lam0 : ℝ) (a : l1Weighted ν) : F lam0 a = sq a - c lam0 := rfl

/-- Sequence-level formula for F(a): CauchyProduct(a,a) - paramSeq(λ₀).
Bridges the abstract `F` to computable form for certificates. -/
lemma F_toSeq (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (F lam0 a) n =
    CauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq a) n - paramSeq lam0 n := by
  show lpWeighted.toSeq (a * a) n - paramSeq lam0 n = _
  rfl

theorem differentiable_F (lam0 : ℝ) : Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  differentiable_F_sub_const _

theorem fderiv_F (lam0 : ℝ) (a : l1Weighted ν) :
    fderiv ℝ (F lam0) a = (2 : ℝ) • leftMul a :=
  fderiv_F_sub_const _ _

/-- Approximate solution: finite coefficients ā₀, ..., āₙ with ā₀ ≠ 0. -/
structure ApproxSolution (N : ℕ) where
  aBar_fin : Fin (N + 1) → ℝ
  aBar_zero_ne : aBar_fin 0 ≠ 0

/-- Zero-padded extension to ℕ. -/
def ApproxSolution.toSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ := fun n =>
  if h : n ≤ N then sol.aBar_fin ⟨n, Nat.lt_succ_of_le h⟩ else 0

lemma ApproxSolution.toSeq_zero_of_gt {N : ℕ} (sol : ApproxSolution N) (n : ℕ) (hn : N < n) :
    sol.toSeq n = 0 := by
  simp only [ApproxSolution.toSeq, not_le.mpr hn, ↓reduceDIte]

lemma ApproxSolution.toSeq_eq_fin {N : ℕ} (sol : ApproxSolution N) (n : Fin (N + 1)) :
    sol.toSeq n = sol.aBar_fin n := by
  simp only [ApproxSolution.toSeq, Fin.is_le, ↓reduceDIte]

lemma ApproxSolution.mem {N : ℕ} (sol : ApproxSolution N) : lpWeighted.Mem ν 1 sol.toSeq := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp only [toSeq, mul_eq_zero, abs_eq_zero, dite_eq_right_iff, pow_eq_zero_iff',
    PosReal.coe_ne_zero, ne_eq, false_and, or_false]; intros; omega

def ApproxSolution.toL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  lpWeighted.mk sol.toSeq sol.mem

@[simp]
lemma ApproxSolution.toL1_toSeq {N : ℕ} (sol : ApproxSolution N) :
    lpWeighted.toSeq (sol.toL1 : l1Weighted ν) = sol.toSeq := rfl

/-! ## 3. Operators A and A† as ScalarBlockDiagData -/

/-- DF^(N)(ā): lower triangular with (DF)_{i,j} = 2*ā_{i-j} for j ≤ i. -/
def dfFin {N : ℕ} (sol : ApproxSolution N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) ≤ i then
    2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0

/-- A† as ScalarBlockDiagData: DF^(N)(ā) on finite, 2ā₀ on tail. -/
def approxDeriv {N : ℕ} (sol : ApproxSolution N) : ScalarBlockDiagData N :=
  ScalarBlockDiagData.ofParts
    (dfFin sol)
    (fun _ => 2 * sol.aBar_fin 0)
    |2 * sol.aBar_fin 0|
    (fun _ _ => le_refl _)

/-- A as ScalarBlockDiagData: A_mat on finite, 1/(2ā₀) on tail. -/
def approxInverse {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ScalarBlockDiagData N :=
  ScalarBlockDiagData.ofParts
    A_mat
    (fun _ => 1 / (2 * sol.aBar_fin 0))
    |1 / (2 * sol.aBar_fin 0)|
    (fun _ _ => le_refl _)

/-- Tail diagonals of A and A† multiply to 1. -/
lemma tailCancel {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n, N < n → (approxInverse sol A_mat).tailDiag0 n *
      (approxDeriv sol).tailDiag0 n = 1 := by
  intro n _
  simp only [approxInverse, approxDeriv, ScalarBlockDiagData.ofParts,
    ScalarBlockDiagData.tailDiag0]
  field_simp [sol.aBar_zero_ne]

/-- Tail diagonal of A is nonzero (for injectivity). -/
lemma approxInverse_tailDiag_ne_zero {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n, N < n → (approxInverse sol A_mat).tailDiag0 n ≠ 0 := by
  intro n _
  simp only [approxInverse, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.tailDiag0,
    ne_eq, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, sol.aBar_zero_ne,
    or_self, not_false_eq_true]

/-! ## 4. Structural Bound Reductions -/

/-! ### Z₀: reduces to finWeightedMatrixNorm of defect matrix -/

/-- Z₀ bound via tail cancellation. -/
lemma Z₀_structural {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Z₀_norm ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤
    l1Weighted.finWeightedMatrixNorm ν
      (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) :=
  ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel
    (ν := ν) _ _ (tailCancel sol A_mat)

/-! ### Z₁: A†-DF kills finite modes, norm bounded by shifted convolution -/

/-- The finite block of `approxDeriv` is a Cauchy matrix with `a_seq = 2 * sol.toSeq`. -/
lemma approxDeriv_finBlock_eq_cauchy {N : ℕ} (sol : ApproxSolution N)
    (i j : Fin (N + 1)) :
    (approxDeriv sol).finBlock0 i j =
    if (j : ℕ) ≤ i then (fun k => 2 * sol.toSeq k) ((i : ℕ) - (j : ℕ)) else 0 := by
  simp only [approxDeriv, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.finBlock0,
    dfFin, Matrix.of_apply]
  split_ifs with h
  · rw [← sol.toSeq_eq_fin]
  · rfl

/-- A† - DF(ā) kills finite modes for x²-λ.
Uses `toScalarCLM_toSeq_fin_eq_cauchy`: on finite modes, the block-diagonal action
equals the Cauchy product, which is exactly 2·leftMul(ā). -/
lemma approxDeriv_sub_fderiv_fin_kill {N : ℕ}
    (sol : ApproxSolution N) (lam0 : ℝ) (h : l1Weighted ν)
    (n : ℕ) (hn : n ≤ N) :
    lpWeighted.toSeq (((approxDeriv sol).toScalarCLM (ν := ν) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν)) h) n = 0 := by
  simp only [ContinuousLinearMap.sub_apply, lpWeighted.sub_toSeq, fderiv_F,
    ContinuousLinearMap.smul_apply, leftMul_apply, lpWeighted.smul_toSeq]
  -- Goal: A†(h)[n] - 2*(ā·h)[n] = 0
  -- A†(h)[n] = CauchyProduct(2*toSeq, h)[n] via the Cauchy bridge
  rw [ScalarBlockDiagData.toScalarCLM_toSeq_fin_eq_cauchy (approxDeriv sol)
    (fun k => 2 * sol.toSeq k) (approxDeriv_finBlock_eq_cauchy sol) h n hn]
  -- 2*(ā·h)[n] = CauchyProduct(2*toSeq, h)[n]
  have hmul : 2 * lpWeighted.toSeq ((sol.toL1 : l1Weighted ν) * h) n =
      CauchyProduct (fun k => 2 * sol.toSeq k) (lpWeighted.toSeq h) n := by
    have : lpWeighted.toSeq ((sol.toL1 : l1Weighted ν) * h) n =
      CauchyProduct sol.toSeq (lpWeighted.toSeq h) n := rfl
    rw [this, CauchyProduct.apply, CauchyProduct.apply]; simp [Finset.mul_sum, mul_assoc]
  rw [hmul, sub_self]

/-! ### Shifted coefficient sequence for Z₁ norm bound -/

/-- Shifted sequence: ā with 0th coefficient zeroed. Supported on [1,N]. -/
def shiftedSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ :=
  fun k => if k ∈ Finset.Icc 1 N then sol.toSeq k else 0

lemma shiftedSeq_mem {N : ℕ} (sol : ApproxSolution N) :
    lpWeighted.Mem ν 1 (shiftedSeq sol) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
  intro n hn; simp [shiftedSeq, hn]

/-- Shifted sequence as element of ℓ¹_ν. -/
def shiftedL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  lpWeighted.mk (shiftedSeq sol) (shiftedSeq_mem sol)

lemma shiftedL1_norm {N : ℕ} (sol : ApproxSolution N) :
    ‖@shiftedL1 ν N sol‖ = ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n := by
  rw [l1Weighted.norm_eq_tsum]
  have h_eq : ∀ n, |lpWeighted.toSeq (@shiftedL1 ν N sol) n| * (ν : ℝ) ^ n =
      if n ∈ Finset.Icc 1 N then |sol.toSeq n| * (ν : ℝ) ^ n else 0 := by
    intro n; simp only [shiftedL1, lpWeighted.mk_apply, shiftedSeq]
    split_ifs <;> simp [abs_zero]
  simp_rw [h_eq]; rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl; intro n hn; simp [hn]
  · intro n hn; simp [hn]

/-- On tail modes n > N, the difference A†-DF acts as -2·leftMul(shiftedL1).
The tail diagonal of A† gives 2ā₀·h_n, while DF gives 2·CauchyProduct(ā,h)_n.
Since ā has support [0,N] and n > N, the Cauchy product splits as
ā₀·h_n + ∑_{k∈[1,N]} ā_k·h_{n-k}, so the difference is -2·∑_{k∈[1,N]} ā_k·h_{n-k}. -/
lemma approxDeriv_sub_fderiv_tail_eq {N : ℕ}
    (sol : ApproxSolution N) (lam0 : ℝ) (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq (((approxDeriv sol).toScalarCLM (ν := ν) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν)) h) n =
    -(2 : ℝ) * lpWeighted.toSeq ((shiftedL1 sol : l1Weighted ν) * h) n := by
  simp only [ContinuousLinearMap.sub_apply, lpWeighted.sub_toSeq, fderiv_F,
    ContinuousLinearMap.smul_apply, leftMul_apply, lpWeighted.smul_toSeq]
  -- LHS: tail diagonal gives 2ā₀·h_n
  rw [ScalarBlockDiagData.toScalarCLM_toSeq_tail (approxDeriv sol) h n hn]
  simp only [approxDeriv, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.tailDiag0]
  -- RHS: expand both Cauchy products
  have hmul_full : lpWeighted.toSeq ((sol.toL1 : l1Weighted ν) * h) n =
      CauchyProduct sol.toSeq (lpWeighted.toSeq h) n := rfl
  have hmul_shifted : lpWeighted.toSeq ((shiftedL1 sol : l1Weighted ν) * h) n =
      CauchyProduct (shiftedSeq sol) (lpWeighted.toSeq h) n := rfl
  rw [hmul_full, hmul_shifted]
  -- Split full Cauchy product: a₀·h_n + ∑_{k∈[1,N]} a_k·h_{n-k}
  rw [CauchyProduct.apply_of_support_le_split
    (fun k hk => sol.toSeq_zero_of_gt k hk) hn]
  -- Split shifted Cauchy product similarly
  rw [CauchyProduct.apply_of_support_le_split
    (fun k (hk : N < k) => by simp [shiftedSeq, Finset.mem_Icc]; omega) hn]
  -- Simplify shiftedSeq: 0 ∉ [1,N] gives 0, k ∈ [1,N] gives sol.toSeq k
  have h_shifted_sum :
      shiftedSeq sol 0 * lpWeighted.toSeq h n +
      ∑ k ∈ Finset.Icc 1 N, shiftedSeq sol k * lpWeighted.toSeq h (n - k) =
      ∑ k ∈ Finset.Icc 1 N, sol.toSeq k * lpWeighted.toSeq h (n - k) := by
    simp only [shiftedSeq, show (0 : ℕ) ∉ Finset.Icc 1 N from by simp [Finset.mem_Icc],
      ite_false, zero_mul, zero_add]
    exact Finset.sum_congr rfl (fun k hk => by simp [hk])
  rw [h_shifted_sum, show sol.aBar_fin (0 : Fin (N + 1)) = sol.toSeq 0 from
    (sol.toSeq_eq_fin 0).symm]
  ring

/-- **Z₁ pipeline**: Uses `Z₁_le_of_fin_kill_tail_dom` (general API) with
E = -2•leftMul(shiftedL1) as the dominating operator. Certificate provides C. -/
lemma Z₁_le_via_eval {N : ℕ} {ν : PosReal}
    (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam0 : ℝ)
    (C : ℝ)
    (hbound : (approxInverse sol A_mat).tailBound *
      (2 * ∑ m ∈ Finset.Icc 1 N, |sol.toSeq m| * (ν : ℝ) ^ m) ≤ C) :
    ‖((approxInverse sol A_mat).toScalarCLM (ν := ν)).comp
      ((approxDeriv sol).toScalarCLM (ν := ν) -
        fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν))‖ ≤ C :=
  ScalarBlockDiagData.Z₁_le_of_fin_kill_tail_dom N (approxInverse sol A_mat)
    _ ((-2 : ℝ) • leftMul (shiftedL1 sol))
    (fun h n hn => approxDeriv_sub_fderiv_fin_kill sol lam0 h n hn)
    (fun h n hn => by
      rw [approxDeriv_sub_fderiv_tail_eq sol lam0 h n hn]; simp [leftMul_apply])
    C (hbound.trans' (mul_le_mul_of_nonneg_left
      ((norm_smul (-2 : ℝ) (leftMul (shiftedL1 sol : l1Weighted ν)) ▸ by
        rw [norm_neg, Real.norm_ofNat]
        exact mul_le_mul_of_nonneg_left
          ((norm_leftMul_le _).trans_eq (shiftedL1_norm sol)) (by positivity)))
      (approxInverse sol A_mat).tailBound_nonneg))

/-! ### Z₂: reduces to 2 * ‖A‖ * r₀ -/

/-- Z₂ structural bound: ‖A ∘ (DF(c) - DF(ā))‖ ≤ 2 * ‖A‖ * ‖c - ā‖. -/
lemma Z₂_structural {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (lam0 : ℝ) (c_val : l1Weighted ν) :
    Z₂_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν)) c_val ≤
    2 * ‖(approxInverse sol A_mat).toScalarCLM (ν := ν)‖ *
      ‖c_val - (sol.toL1 : l1Weighted ν)‖ := by
  show ‖_‖ ≤ _
  rw [show fderiv ℝ (F lam0) c_val - fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν) =
      (2 : ℝ) • leftMul (c_val - sol.toL1) from fderiv_F_diff_eq _ _ _]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_smul, Real.norm_ofNat]
  have := norm_leftMul_le (ν := ν) (c_val - sol.toL1)
  have := norm_nonneg ((approxInverse sol A_mat).toScalarCLM (ν := ν))
  nlinarith

/-! ### Z₂ corollary: for c ∈ closedBall(ā, r₀) -/

lemma Z₂_ball_bound {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (lam0 : ℝ) (r₀ : ℝ) (Z₂_val : ℝ)
    (hA : 2 * ‖(approxInverse sol A_mat).toScalarCLM (ν := ν)‖ ≤ Z₂_val)
    (c_val : l1Weighted ν)
    (hc : c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀) :
    Z₂_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν)) c_val ≤
    Z₂_val * r₀ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  exact (Z₂_structural sol A_mat lam0 c_val).trans
    ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hc (le_trans (by positivity) hA)))

/-! ### Main theorem skeleton -/

/-- Generic existence/uniqueness for Example 7.7 via `existsUnique_of_scalar_bounds`. -/
theorem existsUnique {N : ℕ} (sol : ApproxSolution N)
    (A_mat : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (lam0 : ℝ) {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν)) ≤ Y₀)
    (hZ₀ : Z₀_norm ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤ Z₀)
    (hZ₁ : Z₁_norm (F lam0) sol.toL1
      ((approxInverse sol A_mat).toScalarCLM (ν := ν))
      ((approxDeriv sol).toScalarCLM (ν := ν)) ≤ Z₁)
    (hZ₂ : ∀ c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      Z₂_norm (F lam0) sol.toL1
        ((approxInverse sol A_mat).toScalarCLM (ν := ν)) c_val ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (h_inj : Function.Injective
      ((approxInverse sol A_mat).toScalarCLM (ν := ν))) :
    ∃! xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 xTilde = 0 :=
  ScalarBlockDiagData.existsUnique_of_scalar_bounds
    (approxInverse sol A_mat) (approxDeriv sol)
    hr₀ hY₀ hZ₀ hZ₁ hZ₂ (differentiable_F lam0) h_radii h_inj

end Example77

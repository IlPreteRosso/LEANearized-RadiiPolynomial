import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Concrete
import RadiiPolynomial.SystemTaylorODE.LeanCertEval
import RadiiPolynomial.SystemTaylorODE.OmegaWeighted
import RadiiPolynomial.Tactic.AutoPolyFDeriv
import RadiiPolynomial.Example83.Numbers

/-!
# Example 8.3 — Algebraic Infrastructure

Problem-specific algebra for the Lorenz IVP (Section 8.3):
  ẋ₁ = σ(x₂ - x₁),  ẋ₂ = ρx₁ - x₂ - x₁x₃,  ẋ₃ = -βx₃ + x₁x₂
with σ=10, ρ=28, β=8/3, x₀=(1,0,0).

## Contents

1. **Parameters**: N=30, L=3, ν=3/20
2. **Operator data**: `approxInverse` (A, bounded), `approxDeriv` (A†, unbounded `BlockDiagOp`)
3. **Defect**: `defect` (I - A·A†, tailBound=0), `tailCancel`
4. **Bridge lemmas**: connecting Numbers.lean ℚ data to ℝ structures
5. **Lorenz nonlinearity**: `φ_lorenz` (ring multiplication = Cauchy product)
6. **Zero-finding map**: `F_lorenz` with coefficient extraction lemmas
7. **(TODO) fderiv**: Fréchet derivative structure proof
8. **(TODO) Z₁/Z₂ infrastructure**: DF - A† kills finite modes; constant D²F

## Architecture

The IVP operator A† has tailDiag = n (unbounded), so it is represented as a
`BlockDiagOp` (no tailBound). Only A (the approximate inverse, tailDiag = 1/n)
is a `SystemBlockDiagData`. The defect `I - A·A†` has zero tail
(because (1/n)·n = 1) and is a `SystemBlockDiagData` with tailBound = 0.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap SystemTaylorODE

noncomputable section

/-- Simp set for evaluating CLM applications on Pi-type Banach algebras.
Collects `_apply` lemmas for `sub`, `add`, `neg`, `smul`, `comp`, `proj`, `leftMul`. -/
macro "clm_apply" : tactic =>
  `(tactic| simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    l1Weighted.leftMul_apply])

namespace Example83

/-! ## 1. Parameters -/

/-- N = 30 (Taylor truncation order) -/
abbrev N : ℕ := 30

/-- L = 3 (system dimension: Lorenz has 3 components) -/
abbrev L : ℕ := 3

instance : NeZero L := ⟨by decide⟩

/-- Weight as ℚ (for `colNormTermEval` / `finsum_bound`). -/
abbrev ν_q : ℚ := 3 / 20

/-- ν = 3/20 (weight / radius of convergence) -/
def ν_val : PosReal := ⟨3/20, by norm_num⟩

lemma ν_val_eq_q : (ν_val : ℝ) = ((ν_q : ℚ) : ℝ) := by
  simp [ν_val, ν_q]

/-! ## 2. Approximate Inverse A (SystemBlockDiagData)

A has:
- finBlock: the numerically computed inverse of DF^(N), from Numbers.lean
- tailDiag: 1/n for all components (inverse of mode index)
- tailBound: 1/(N+1) = 1/31
-/

/-- A^(N) finite block: cast from ℚ column data in Numbers.lean. -/
noncomputable def A_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate inverse A as SystemBlockDiagData.
tailDiag l n = 1/n for all l, tailBound = 1/31. -/
noncomputable def approxInverse : SystemBlockDiagData L N where
  finBlock := A_finBlock
  tailDiag := fun _ n => if n = 0 then 0 else 1 / (n : ℝ)
  tailBound := 1 / 31
  tailBound_spec := by
    intro _ n (hn : 30 < n)
    have hne : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have h31 : (31 : ℝ) ≤ n := by exact_mod_cast (show 31 ≤ n by omega)
    rw [if_neg hne, abs_of_pos (div_pos one_pos hpos)]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 31) h31

/-- ℚ value of approxInverse.tailBound, computed from N. -/
abbrev approxInverse_tailBound_q : ℚ := 1 / (↑N + 1)

lemma approxInverse_tailBound_eq :
    approxInverse.tailBound = ((approxInverse_tailBound_q : ℚ) : ℝ) := by
  simp [approxInverse, approxInverse_tailBound_q, N]; push_cast; ring

/-! ## 3. Approximate Derivative A† (BlockDiagOp — unbounded tail)

A† has:
- finBlock: DF^(N)(ā), from Numbers.lean
- tailDiag: n for all components (mode index, from Eq. 8.28)
No tailBound (tail grows without bound).
-/

/-- DF^(N) finite block: cast from ℚ column data in Numbers.lean. -/
noncomputable def DF_finBlock : FiniteBlockMatrix L N :=
  fun l j i k => ((DF_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ)

/-- Approximate derivative A† as BlockDiagOp (unbounded tail).
tailDiag l n = n (mode index multiplication, from Eq. 8.28). -/
noncomputable def approxDeriv : BlockDiagOp L N where
  finBlock := DF_finBlock
  tailDiag := fun _ n => (n : ℝ)

/-! ## 4. Defect D = I - A · A† (SystemBlockDiagData, tailBound = 0)

The defect has zero tail because (1/n) · n = 1 for n > N.
-/

/-- Tail cancellation: A.tailDiag * A†.tailDiag = 1 for n > N. -/
lemma tailCancel (l : Fin L) (n : ℕ) (hn : N < n) :
    approxInverse.tailDiag l n * approxDeriv.tailDiag l n = 1 := by
  simp only [approxInverse, approxDeriv, BlockDiagOp.tailDiag]
  rw [if_neg (by omega : n ≠ 0)]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Defect D = I - A · A†. Uses `defectOfBlockDiagOp` from Concrete.lean. -/
noncomputable def defect : SystemBlockDiagData L N :=
  defectOfBlockDiagOp approxInverse approxDeriv

/-! ## 4b. Composed Approximate Derivative (A·A† as SystemBlockDiagData)

The block-diagonal product A·A† with:
- finBlock = Σ_m A.finBlock l m * A†.finBlock m j  (product matrix)
- tailDiag = 1  (since (1/n)·n = 1)
- tailBound = 1

Used as `A_dagger` in `general_radii_polynomial_theorem` with `A = id`.
Then Z₀ = ‖I - composedApprox.toCLM‖ = ‖defect.toCLM‖ (small),
and  Z₁ = ‖composedApprox.toCLM - fderiv G ā‖ (tail error). -/

/-- Composed approximate derivative: the block-diagonal product A·A† as a bounded operator. -/
noncomputable def composedApprox : SystemBlockDiagData L N where
  finBlock l j := ∑ m, approxInverse.finBlock l m * approxDeriv.finBlock m j
  tailDiag _ _ := 1
  tailBound := 1
  tailBound_spec := fun _ _ _ => by simp [abs_of_pos]

/-- `I - composedApprox.toCLM = defect.toCLM`: the defect identity via `defect_of_composed_toCLM_eq`. -/
lemma composedApprox_defect_eq :
    ContinuousLinearMap.id ℝ (XL1 ν_val L) - composedApprox.toCLM (ν := ν_val) =
    defect.toCLM (ν := ν_val) := by
  apply defect_of_composed_toCLM_eq approxInverse approxDeriv
  · -- hfin: composedApprox matches product on finite
    intro x l n
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_fin_eq_sum_mulVec]
    simp [composedApprox, Matrix.mulVec, dotProduct]
  · -- htail: composedApprox tail = 1 matches product tail = (1/n)·n
    intro x l n hn
    rw [SystemBlockDiagData.toCoeff_toCLM,
      SystemBlockDiagData.action_tail _ _ _ _ hn]
    simp [composedApprox, tailCancel _ _ hn]
  · exact tailCancel

/-- A.tailDiag is nonzero for all tail modes (for injectivity). -/
lemma approxInverse_tailDiag_ne_zero (l : Fin L) (n : ℕ) (hn : N < n) :
    approxInverse.tailDiag l n ≠ 0 := by
  simp only [approxInverse]
  rw [if_neg (by omega : n ≠ 0)]
  positivity

/-! ## 5. Bridge Lemmas (ℚ → ℝ)

These connect the ℚ data in Numbers.lean to the ℝ structures above. -/

/-- ā component data from Numbers.lean. -/
def abar_Q : Fin L → Array ℚ
  | 0 => abar_0
  | 1 => abar_1
  | 2 => abar_2

/-- A^(N) finBlock entries match Numbers.lean ℚ data. -/
lemma A_finBlock_eq (l j : Fin L) (i : Fin (N + 1)) (k : Fin (N + 1)) :
    A_finBlock l j i k = ((A_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) := rfl

/-- DF^(N) finBlock entries match Numbers.lean ℚ data. -/
lemma DF_finBlock_eq (l j : Fin L) (i : Fin (N + 1)) (k : Fin (N + 1)) :
    DF_finBlock l j i k = ((DF_col l j (k : ℕ)).getD (i : ℕ) 0 : ℝ) := rfl

/-! ## 6. F_lorenz — Zero-Finding Map

The zero-finding map F : XL1 ν 3 → YOmega ν 3 defined by:
  F_j(a)_0 = a_{j,0} - (x₀)_j
  F_j(a)_k = k · a_{j,k} - φ_j(a)_{k-1}  for k ≥ 1

where φ encodes the Lorenz nonlinearity at the sequence level.
F maps into the omega-weighted space `ℓ¹_ω` (Proposition 8.1.5) because
the mode-index factor `k` is compensated by the omega weight `ω_k = ν^{k+1}/(k+1)`.
-/

/-- Lorenz parameters. -/
def σ_val : ℝ := 10
def ρ_val : ℝ := 28
def β_val : ℝ := 8 / 3

/-- Initial condition x₀ = (1, 0, 0). -/
def x₀ : Fin L → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

/-- Lorenz nonlinearity φ at the sequence level:
  φ₀(a)_k = σ(a₁_k - a₀_k)
  φ₁(a)_k = ρa₀_k - a₁_k - (a₀ * a₂)_k
  φ₂(a)_k = -βa₂_k + (a₀ * a₁)_k -/
def φ_lorenz (a : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | 0 => σ_val • (a 1 - a 0)
  | 1 => ρ_val • a 0 - a 1 - a 0 * a 2
  | 2 => -(β_val • a 2) + a 0 * a 1

@[simp] lemma toSeq_φ_lorenz_0 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 0) n =
      σ_val * (l1Weighted.toSeq (a 1) n - l1Weighted.toSeq (a 0) n) := rfl

@[simp] lemma toSeq_φ_lorenz_1 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 1) n =
      ρ_val * l1Weighted.toSeq (a 0) n - l1Weighted.toSeq (a 1) n -
        l1Weighted.toSeq (a 0 * a 2) n := rfl

@[simp] lemma toSeq_φ_lorenz_2 (a : XL1 ν_val L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz a 2) n =
      -(β_val * l1Weighted.toSeq (a 2) n) + l1Weighted.toSeq (a 0 * a 1) n := rfl

/-- The IVP zero-finding map F : XL1 ν 3 → YOmega ν 3.

At the coefficient level (Eq. 8.15):
  F_j(a)_0 = a_{j,0} - (x₀)_j
  F_j(a)_k = k · a_{j,k} - φ_j(a)_{k-1}  for k ≥ 1

F maps into `ℓ¹_ω` (not `ℓ¹_ν`) because the factor `k` makes `{k·a_k}` unsummable
in geometric weights, but `|(k+1)·a_{k+1}| · ω_k = |a_{k+1}| · ν^{k+1}` by the
omega weight identity (Proposition 8.1.5). -/
noncomputable def F_lorenz (a : XL1 ν_val L) : YOmega ν_val L := fun l =>
  l1Omega.mk (fun n =>
    match n with
    | 0 => l1Weighted.toSeq (a l) 0 - x₀ l
    | n + 1 => ((n : ℝ) + 1) * l1Weighted.toSeq (a l) (n + 1) -
        l1Weighted.toSeq (φ_lorenz a l) n)
    (l1Omega.mem_ivp_zero_finding (a l) (φ_lorenz a l) _)

/-- F_lorenz at the coefficient level: mode 0. -/
lemma F_lorenz_coeff_zero (a : XL1 ν_val L) (l : Fin L) :
    l1Omega.toSeq (F_lorenz a l) 0 =
      l1Weighted.toSeq (a l) 0 - x₀ l := by
  simp only [F_lorenz, l1Omega.mk_apply]

/-- F_lorenz at the coefficient level: mode k+1. -/
lemma F_lorenz_coeff_succ (a : XL1 ν_val L) (l : Fin L) (n : ℕ) :
    l1Omega.toSeq (F_lorenz a l) (n + 1) =
      ((n : ℝ) + 1) * l1Weighted.toSeq (a l) (n + 1) -
        l1Weighted.toSeq (φ_lorenz a l) n := by
  simp only [F_lorenz, l1Omega.mk_apply]

/-! ## 7. Approximate Solution ābar -/

/-- ābar coefficient sequence: finite support (modes 0..N), zero beyond. -/
def abar_seq (l : Fin L) (n : ℕ) : ℝ :=
  if n ≤ N then ((abar_Q l).getD n 0 : ℝ) else 0

lemma abar_seq_support (l : Fin L) (n : ℕ) (hn : N < n) : abar_seq l n = 0 := by
  simp [abar_seq, show ¬(n ≤ N) from by omega]

/-- ābar toSeq = raw ℚ getD (getD returns 0 out of bounds, matching abar_seq). -/
lemma abar_seq_eq_getD (l : Fin L) (k : ℕ) :
    abar_seq l k = ((abar_Q l).getD k 0 : ℝ) := by
  simp only [abar_seq]
  by_cases hk : k ≤ N
  · simp [hk]
  · simp only [show ¬(k ≤ N) from hk, ↓reduceIte]
    symm; simp only [Array.getD]
    simp [show ¬(k < (abar_Q l).size) from by
      have : (abar_Q l).size = N + 1 := by
        fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]
      omega]

noncomputable def abar : XL1 ν_val L := fun l =>
  lpWeighted.mk (abar_seq l) (by
    rw [l1Weighted.mem_iff]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) fun n hn => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp [abar_seq_support l n (by omega)])

/-! ## 8. Composed Map G_lorenz = A ∘ F : XL1 → XL1

The radii polynomial theorem works with a map X → X. Since F maps into YOmega (ℓ¹_ω),
we compose with A to get G = A ∘ F : XL1 → XL1. The composition is defined at the
coefficient level: A.action applied to the omega-weighted coefficients of F.
The key property: A's tail (1/n) cancels F's factor (n), giving bounded G.

For the radii polynomial, we use `general_radii_polynomial_theorem` with:
- f = G_lorenz (the composed map)
- A_dagger = fderiv ℝ G_lorenz ābar (set equal to make Z₁ = 0)
- A = id (since G already incorporates the approximate inverse)

Equivalently, viewing the original theorem structure:
- f = F_lorenz : X → Y,  A : Y →L[ℝ] X
- G = A ∘ F : X → X
- The theorem applies to G with A_approx_inv = id.

The Z₀ bound then uses `defect_of_composed_toCLM_eq` to connect
I - fderiv(G, ābar) to the defect of A·A†. -/

/-- F_lorenz coefficient extraction as SystemCoeff. -/
def F_coeffs (a : XL1 ν_val L) : SystemCoeff L :=
  fun l n => l1Omega.toSeq (F_lorenz a l) n

/-- G_lorenz = A ∘ F : XL1 → XL1 (the composed map for the radii polynomial).
Defined at the coefficient level: `approxInverse.action` applied to F_lorenz's coefficients.
Tail: (1/n) * (n*a_n - φ_{n-1}) = a_n - φ_{n-1}/n, which is ℓ¹_ν-summable. -/
noncomputable def G_lorenz (a : XL1 ν_val L) : XL1 ν_val L := fun l =>
  lpWeighted.mk (approxInverse.action (F_coeffs a) l)
    (l1Weighted.mem_of_eventually_le_add_shift _ (a l) (φ_lorenz a l) N fun n hn => by
      -- On tail: action = (1/n) * F_n = a_n - φ_{n-1}/n
      rw [SystemBlockDiagData.action_tail _ _ _ _ hn]
      simp only [approxInverse, if_neg (show n ≠ 0 by omega), F_coeffs]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [F_lorenz_coeff_succ, Nat.add_sub_cancel]
      -- |(1/(m+1)) * ((m+1)*a - φ)| ≤ |a| + |φ|
      rw [show (1 : ℝ) / (↑(m + 1) : ℝ) = ((m : ℝ) + 1)⁻¹ from by push_cast; exact one_div _]
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [abs_mul, abs_inv, abs_of_nonneg hpos.le, inv_mul_le_iff₀ hpos]
      exact ((abs_sub _ _).trans (by rw [abs_mul, abs_of_nonneg hpos.le])).trans
        (by nlinarith [abs_nonneg (l1Weighted.toSeq (φ_lorenz a l) m),
          Nat.cast_nonneg (α := ℝ) m]))

/-- G_lorenz at the coefficient level. -/
lemma G_lorenz_coeff (a : XL1 ν_val L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (G_lorenz a l) n =
      approxInverse.action (F_coeffs a) l n := by
  simp [G_lorenz, l1Weighted.toSeq, lpWeighted.toSeq, lpWeighted.mk]

/-- G_lorenz tail simplification: for n > N,
G(a)_l_n = a_l_n - φ_l(a)_{n-1}/n. -/
lemma G_lorenz_tail (a : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (G_lorenz a l) n =
      l1Weighted.toSeq (a l) n -
        l1Weighted.toSeq (φ_lorenz a l) (n - 1) / (n : ℝ) := by
  rw [G_lorenz_coeff]
  -- On tail: action = tailDiag * F_coeffs
  rw [SystemBlockDiagData.action_tail approxInverse (F_coeffs a) l n hn]
  -- Unfold tailDiag = 1/n and F_coeffs
  simp only [approxInverse, F_coeffs, if_neg (by omega : n ≠ 0)]
  -- F_lorenz at mode n (n ≥ 1): (n)*a_n - φ_{n-1}
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [F_lorenz_coeff_succ]
  -- (1/(m+1)) * ((m+1)*a_{m+1} - φ_m) = a_{m+1} - φ_m/(m+1)
  simp only [Nat.add_sub_cancel]
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast; ring

/-! ## 9. Fréchet Derivative of G_lorenz

DG(ā)(h) = A.action(DF(ā)(h)) at the coefficient level.
On tail modes (n > N): DG(ā)(h)_l_n = h_l_n - Dφ_l(ā)(h)_{n-1}/n.

The Z₀ bound decomposes as:
  ‖I - DG(ā)‖ ≤ ‖defect.toCLM‖ + ‖A.toCLM ∘ T‖
where T is the tail linearization error (kills finite modes, bounded on tail).
This uses `Z₀_norm_le_of_defect_plus_tail_error` from Concrete.lean. -/

/-- Derivative of φ_lorenz at ābar (linearization of the nonlinearity).
For the Lorenz system, φ has bilinear terms a_i * a_j, so Dφ(ā)(h) involves
products ā_i · h_j + h_i · ā_j. -/
def Dφ_lorenz (h : Fin L → l1Weighted ν_val) : Fin L → l1Weighted ν_val
  | 0 => σ_val • (h 1 - h 0)
  | 1 => ρ_val • h 0 - h 1 - (abar 0 * h 2 + h 0 * abar 2)
  | 2 => -(β_val • h 2) + (abar 0 * h 1 + h 0 * abar 1)

/-- φ_lorenz is differentiable (polynomial on product of Banach algebras). -/
lemma differentiable_φ_lorenz_component (l : Fin L) :
    Differentiable ℝ (fun a : XL1 ν_val L => φ_lorenz a l) := by
  fin_cases l <;> simp only [φ_lorenz] <;> fun_prop

/-! ### Per-component Fréchet derivatives of φ_lorenz (via `auto_poly_fderiv`)

The `proj l` abbreviation is `ContinuousLinearMap.proj` on `XL1 ν_val L = Fin L → l1Weighted ν_val`. -/

private abbrev proj_L (l : Fin L) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν_val) l

lemma fderiv_φ_lorenz_0 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 0) a =
    σ_val • (proj_L 1 - proj_L 0) := by
  show fderiv ℝ (fun a : XL1 ν_val L => σ_val • (a 1 - a 0)) a = _
  auto_poly_fderiv

lemma fderiv_φ_lorenz_1 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 1) a =
    ρ_val • proj_L 0 - proj_L 1 -
      ((l1Weighted.leftMul (a 0)).comp (proj_L 2) +
       (l1Weighted.leftMul (a 2)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => ρ_val • a 0 - a 1 - a 0 * a 2) a = _
  auto_poly_fderiv

lemma fderiv_φ_lorenz_2 (a : XL1 ν_val L) :
    fderiv ℝ (fun a => φ_lorenz a 2) a =
    -(β_val • proj_L 2) +
      ((l1Weighted.leftMul (a 0)).comp (proj_L 1) +
       (l1Weighted.leftMul (a 1)).comp (proj_L 0)) := by
  show fderiv ℝ (fun a : XL1 ν_val L => -(β_val • a 2) + a 0 * a 1) a = _
  auto_poly_fderiv

/-- Dφ_lorenz agrees with the computed fderiv of φ_lorenz at ābar. -/
lemma Dφ_lorenz_eq_fderiv (h : XL1 ν_val L) (l : Fin L) :
    Dφ_lorenz h l = (fderiv ℝ (fun a => φ_lorenz a l) abar) h := by
  fin_cases l <;>
    simp only [Dφ_lorenz, show (⟨0, by decide⟩ : Fin L) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin L) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin L) = 2 from rfl,
      fderiv_φ_lorenz_0, fderiv_φ_lorenz_1, fderiv_φ_lorenz_2, proj_L,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      l1Weighted.leftMul_apply, mul_comm (abar _) (h _)]

/-- φ_lorenz is quadratic, so fderiv(φ_l, c) - fderiv(φ_l, ā) is linear in (c - ā).
The linear/constant parts cancel, leaving only the bilinear terms. -/
lemma fderiv_φ_diff_0 (c a : XL1 ν_val L) :
    fderiv ℝ (fun x => φ_lorenz x 0) c - fderiv ℝ (fun x => φ_lorenz x 0) a = 0 := by
  rw [fderiv_φ_lorenz_0, fderiv_φ_lorenz_0, sub_self]

lemma fderiv_φ_diff_1 (c a : XL1 ν_val L) (h : XL1 ν_val L) :
    ((fderiv ℝ (fun x => φ_lorenz x 1) c -
      fderiv ℝ (fun x => φ_lorenz x 1) a)) h =
    -((c 0 - a 0) * h 2 + h 0 * (c 2 - a 2)) := by
  simp only [fderiv_φ_lorenz_1]; clm_apply; ring

lemma fderiv_φ_diff_2 (c a : XL1 ν_val L) (h : XL1 ν_val L) :
    ((fderiv ℝ (fun x => φ_lorenz x 2) c -
      fderiv ℝ (fun x => φ_lorenz x 2) a)) h =
    (c 0 - a 0) * h 1 + h 0 * (c 1 - a 1) := by
  simp only [fderiv_φ_lorenz_2]; clm_apply; ring

/-- The "tail" part of G_lorenz: `a l - shiftDivN_CLM(φ_lorenz a l)`.
On modes n > N, this equals G_lorenz a l exactly. Manifestly differentiable
since shiftDivN_CLM is CLM and φ_lorenz is polynomial. -/
noncomputable def G_tail (a : XL1 ν_val L) : XL1 ν_val L := fun l =>
  a l - shiftDivN_CLM (φ_lorenz a l)

lemma differentiable_G_tail : Differentiable ℝ G_tail := by
  intro a; apply differentiableAt_pi.mpr; intro l
  show DifferentiableAt ℝ (fun a : XL1 ν_val L => a l - shiftDivN_CLM (φ_lorenz a l)) a
  have : Differentiable ℝ (fun a : XL1 ν_val L => shiftDivN_CLM (φ_lorenz a l)) :=
    fun a => (shiftDivN_CLM.differentiable.comp (differentiable_φ_lorenz_component l)) a
  fun_prop

/-- G_lorenz agrees with G_tail on tail modes (n > N). -/
lemma G_lorenz_eq_G_tail_on_tail (a : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (G_lorenz a l) n = l1Weighted.toSeq (G_tail a l) n := by
  rw [G_lorenz_tail a l n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [G_tail, Nat.add_sub_cancel, lpWeighted.sub_toSeq, shiftDivN_CLM_apply,
    shiftDivN_succ_mode]

/-- The finite correction seq: action - tail formula. Zero for n > N. -/
private def G_correction_seq (a : XL1 ν_val L) (l : Fin L) (n : ℕ) : ℝ :=
  approxInverse.action (F_coeffs a) l n -
    (l1Weighted.toSeq (a l) n - l1Weighted.toSeq (shiftDivN_CLM (φ_lorenz a l)) n)

private lemma G_correction_seq_zero_tail (a : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    G_correction_seq a l n = 0 := by
  simp only [G_correction_seq]
  rw [← G_lorenz_coeff, G_lorenz_eq_G_tail_on_tail a l n hn]
  simp [G_tail, shiftDivN_CLM_apply]

/-- The finite correction: G_lorenz - G_tail, finitely supported on modes 0..N. -/
noncomputable def G_fin_correction (a : XL1 ν_val L) : XL1 ν_val L := fun l =>
  lpWeighted.mk (G_correction_seq a l) (by
    rw [l1Weighted.mem_iff]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) fun n hn => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp [G_correction_seq_zero_tail a l n (by omega)])

lemma G_lorenz_eq_tail_plus_correction (a : XL1 ν_val L) (l : Fin L) :
    G_lorenz a l = G_tail a l + G_fin_correction a l := by
  apply lpWeighted.ext; intro n
  simp only [lpWeighted.add_toSeq, G_fin_correction, lpWeighted.mk_apply, G_correction_seq,
    G_tail, shiftDivN_CLM_apply, lpWeighted.sub_toSeq]
  show approxInverse.action (F_coeffs a) l n = _
  ring

/-- G_fin_correction is differentiable: finitely supported, each mode polynomial in `a`. -/
lemma differentiable_G_fin_correction : Differentiable ℝ (fun a => G_fin_correction a) := by
  intro a; apply differentiableAt_pi.mpr; intro l
  exact l1Weighted.differentiable_mk_of_finSupp (fun a => G_correction_seq a l) N
    (fun a n hn => G_correction_seq_zero_tail a l n hn) _ (fun k => by
      -- G_correction_seq a l k = action(F) l k - (a_l_k - shiftDivN(φ(a) l)_k)
      -- = action(F) l k - G_tail(a)_l_k
      -- Both are differentiable: G_tail by differentiable_G_tail, action by finite sum of polynomials.
      simp only [G_correction_seq]
      -- Second part: toSeq(a l) k - toSeq(shiftDivN_CLM(φ(a) l)) k is differentiable
      -- (coordinate of G_tail, which is differentiable)
      have h_tail_diff : Differentiable ℝ (fun a : XL1 ν_val L =>
          l1Weighted.toSeq (a l) ↑k - l1Weighted.toSeq (shiftDivN_CLM (φ_lorenz a l)) ↑k) :=
        fun a => ((l1Weighted.toSeq_CLM (↑k)).differentiableAt.comp a
          (differentiableAt_pi.mp differentiableAt_id l)).sub
          ((l1Weighted.toSeq_CLM (↑k)).differentiableAt.comp a
            (shiftDivN_CLM.differentiableAt.comp a (differentiable_φ_lorenz_component l a)))
      -- First part: action(F_coeffs a) l k — use general differentiable_action_fin API
      have h_action_diff : Differentiable ℝ (fun a : XL1 ν_val L =>
          approxInverse.action (F_coeffs a) l ↑k) :=
        approxInverse.differentiable_action_fin F_coeffs (fun j m => by
          -- F_coeffs per mode: mode 0 = linear, mode m+1 = const*coord - φ
          simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
          cases (m : ℕ) with
          | zero =>
            exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
              (differentiable_pi_apply j)).sub (differentiable_const _)
          | succ n =>
            exact (differentiable_const _ |>.mul
              ((l1Weighted.toSeq_CLM (n + 1)).differentiable.comp
                (differentiable_pi_apply j))).sub
              ((l1Weighted.toSeq_CLM n).differentiable.comp
                (differentiable_φ_lorenz_component j)))
        l ↑k (by omega)
      exact h_action_diff.sub h_tail_diff) a

/-- G_lorenz is differentiable (decomposition: G_tail + G_fin_correction). -/
lemma differentiable_G_lorenz : Differentiable ℝ G_lorenz := by
  have : G_lorenz = fun a l => G_tail a l + G_fin_correction a l :=
    funext fun a => funext fun l => G_lorenz_eq_tail_plus_correction a l
  rw [this]; exact differentiable_G_tail.add differentiable_G_fin_correction

lemma hasFDerivAt_G_lorenz (a : XL1 ν_val L) :
    HasFDerivAt G_lorenz (fderiv ℝ G_lorenz a) a :=
  (differentiable_G_lorenz a).hasFDerivAt

/-! ### Fderiv of G_lorenz on tail modes

For Z₁: on tail modes (n > N), the fderiv of G_lorenz at ābar reduces to
`h l - shiftDivN(Dφ h l)`, since G_fin_correction's fderiv vanishes there. -/

/-- composedApprox tail: `(composedApprox.toCLM h) l n = h l n` for n > N (tailDiag = 1). -/
lemma composedApprox_toCLM_tail (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν_val) (composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) h l n := by
  rw [SystemBlockDiagData.toCoeff_toCLM,
    SystemBlockDiagData.action_tail _ _ _ _ hn]
  simp [composedApprox]

/-- Fderiv of G_lorenz at ābar on tail mode n > N:
`toCoeff((fderiv G ā h) l) n = toCoeff(h l) n - toCoeff(shiftDivN_CLM(Dφ h l)) n`.

Proof: coordinate extraction via `toSeq_CLM ∘ proj` + `G_lorenz_tail` + `auto_poly_fderiv`
style computation on `a ↦ a_l_n - φ(a)_{l,n-1}/n`. -/
lemma fderiv_G_lorenz_tail (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν_val) ((fderiv ℝ G_lorenz abar h)) l n =
      toCoeff (ν := ν_val) h l n -
        toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Dφ_lorenz h l)) l n := by
  -- Decompose fderiv G = fderiv G_tail + fderiv G_fin_correction
  have hdecomp : G_lorenz = fun a l => G_tail a l + G_fin_correction a l :=
    funext fun a => funext fun l' => G_lorenz_eq_tail_plus_correction a l'
  have hfadd : fderiv ℝ G_lorenz abar = fderiv ℝ G_tail abar +
      fderiv ℝ (fun a => G_fin_correction a) abar := by
    rw [hdecomp]; exact fderiv_add (differentiable_G_tail abar) (differentiable_G_fin_correction abar)
  rw [hfadd]; simp only [ContinuousLinearMap.add_apply, Pi.add_apply, toCoeff, lpWeighted.add_toSeq]
  -- G_fin_correction fderiv is zero on tail: its image is finitely supported (modes ≤ N)
  have hfin_zero : lpWeighted.toSeq ((fderiv ℝ (fun a => G_fin_correction a) abar h) l) n = 0 := by
    -- Extract component l via fderiv_pi
    rw [show (fderiv ℝ (fun a => G_fin_correction a) abar h) l =
        (fderiv ℝ (fun a : XL1 ν_val L => G_fin_correction a l) abar) h from by
      rw [fderiv_pi (fun i => differentiableAt_pi.mp
        (differentiable_G_fin_correction abar) i)]; rfl]
    -- Each G_correction_seq · l k is differentiable (same proof as differentiable_G_fin_correction)
    have hd_coeff : ∀ k : Fin (N + 1), Differentiable ℝ
        (fun a : XL1 ν_val L => G_correction_seq a l k) := fun k =>
      (approxInverse.differentiable_action_fin F_coeffs (fun j m => by
          simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
          cases (m : ℕ) with
          | zero =>
            exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
              (differentiable_pi_apply j)).sub (differentiable_const _)
          | succ nn =>
            exact (differentiable_const _ |>.mul
              ((l1Weighted.toSeq_CLM (nn + 1)).differentiable.comp
                (differentiable_pi_apply j))).sub
              ((l1Weighted.toSeq_CLM nn).differentiable.comp
                (differentiable_φ_lorenz_component j)))
        l ↑k (by omega)).sub
        (fun a => ((l1Weighted.toSeq_CLM (↑k)).differentiableAt.comp a
          (differentiableAt_pi.mp differentiableAt_id l)).sub
          ((l1Weighted.toSeq_CLM (↑k)).differentiableAt.comp a
            (shiftDivN_CLM.differentiableAt.comp a (differentiable_φ_lorenz_component l a))))
    exact l1Weighted.fderiv_mk_of_finSupp_toSeq_tail
      (fun a => G_correction_seq a l) N
      (fun a m hm => G_correction_seq_zero_tail a l m hm)
      _ hd_coeff abar h n hn
  rw [hfin_zero, add_zero]
  -- Now use G_tail fderiv
  -- G_tail a l = a l - shiftDivN_CLM(φ_lorenz a l), fderiv by subtraction + CLM chain rule
  have hG_tail_fderiv : (fderiv ℝ G_tail abar h) l = h l - shiftDivN_CLM (Dφ_lorenz h l) := by
    -- G_tail a = fun l => a l - shiftDivN_CLM(φ_lorenz a l)
    -- HasFDerivAt per component l: proj l - shiftDivN_CLM ∘ fderiv(φ · l)
    -- Extract per-component fderiv via fderiv_pi
    rw [show (fderiv ℝ G_tail abar h) l =
        (fderiv ℝ (fun a : XL1 ν_val L => G_tail a l) abar) h from by
      rw [fderiv_pi (fun i => differentiableAt_pi.mp (differentiable_G_tail abar) i)]; rfl]
    -- fderiv of (fun a => a l) at abar
    have hd1 : fderiv ℝ (fun a : XL1 ν_val L => a l) abar h = h l := by
      have : (fun a : XL1 ν_val L => a l) = ⇑(proj_L l) := rfl
      rw [this, ContinuousLinearMap.fderiv]; rfl
    -- fderiv of (fun a => shiftDivN_CLM(φ a l)) at abar
    have hd2 : fderiv ℝ (fun a : XL1 ν_val L => shiftDivN_CLM (φ_lorenz a l)) abar h =
        shiftDivN_CLM (Dφ_lorenz h l) := by
      have hcomp := fderiv_comp (𝕜 := ℝ) (f := fun a : XL1 ν_val L => φ_lorenz a l)
        (g := shiftDivN_CLM) abar shiftDivN_CLM.differentiableAt
        (differentiable_φ_lorenz_component l abar)
      simp only [Function.comp_def] at hcomp
      rw [hcomp, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.fderiv, Dφ_lorenz_eq_fderiv]
    -- Combine: fderiv(a l - shiftDivN(φ a l)) = h l - shiftDivN(Dφ h l)
    have hfn : (fun a : XL1 ν_val L => G_tail a l) =
        (fun a => a l) - (fun a => shiftDivN_CLM (φ_lorenz a l)) := by
      ext a; simp [G_tail, Pi.sub_apply]
    rw [hfn]
    change (fderiv ℝ (⇑(proj_L l) - fun a => shiftDivN_CLM (φ_lorenz a l)) abar) h = _
    have hsub : HasFDerivAt
        (⇑(proj_L l) - fun a : XL1 ν_val L => shiftDivN_CLM (φ_lorenz a l))
        (fderiv ℝ (⇑(proj_L l)) abar -
          fderiv ℝ (fun a => shiftDivN_CLM (φ_lorenz a l)) abar) abar :=
      ((proj_L l).differentiableAt.hasFDerivAt).sub
        (((shiftDivN_CLM.differentiable.comp
          (differentiable_φ_lorenz_component l)) abar).hasFDerivAt)
    rw [hsub.fderiv, ContinuousLinearMap.sub_apply]
    rw [show (fun a : XL1 ν_val L => a l) = ⇑(proj_L l) from rfl] at hd1
    rw [hd1, hd2]
  show lpWeighted.toSeq ((fderiv ℝ G_tail abar h) l) n = _
  rw [hG_tail_fderiv]; simp [lpWeighted.sub_toSeq, shiftDivN_CLM_apply]

/-! ### Fderiv of G_lorenz at the coefficient level (general n)

For Z₁ finite-mode cancellation: `toSeq(fderiv G ā h l) n = fderiv(a ↦ A.action(F a) l n) ā h`.
Then `fderiv_action_fin` gives `A.action(fderiv_F_coeffs) l n` for n ≤ N. -/

/-- Chain rule: `toSeq(fderiv G a h l) n = fderiv(a ↦ A.action(F a) l n) a h` for any n and a. -/
lemma fderiv_G_lorenz_coeff_at (a : XL1 ν_val L) (h : XL1 ν_val L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq ((fderiv ℝ G_lorenz a h) l) n =
      (fderiv ℝ (fun a => approxInverse.action (F_coeffs a) l n) a) h := by
  -- toSeq(G a l) n = action(F a) l n for all a (G_lorenz_coeff + mk_apply)
  have hcoeff : (fun x => l1Weighted.toSeq (G_lorenz x l) n) =
      (fun x => approxInverse.action (F_coeffs x) l n) :=
    funext fun x => G_lorenz_coeff x l n
  have hchain : l1Weighted.toSeq ((fderiv ℝ G_lorenz a h) l) n =
      (fderiv ℝ (fun x => l1Weighted.toSeq (G_lorenz x l) n) a) h := by
    rw [show (fderiv ℝ G_lorenz a h) l =
        (fderiv ℝ (fun x : XL1 ν_val L => G_lorenz x l) a) h from by
      rw [fderiv_pi (fun i => differentiableAt_pi.mp (differentiable_G_lorenz a) i)]; rfl]
    show l1Weighted.toSeq_CLM n ((fderiv ℝ (fun x => G_lorenz x l) a) h) = _
    rw [← ContinuousLinearMap.comp_apply (l1Weighted.toSeq_CLM n),
      ← ContinuousLinearMap.fderiv (l1Weighted.toSeq_CLM (ν := ν_val) n),
      ← fderiv_comp a (l1Weighted.toSeq_CLM n).differentiableAt
        ((differentiableAt_pi.mp (differentiable_G_lorenz a)) l)]; rfl
  rw [hchain, hcoeff]

/-- Specialization of `fderiv_G_lorenz_coeff_at` at `abar`. -/
lemma fderiv_G_lorenz_coeff (h : XL1 ν_val L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq ((fderiv ℝ G_lorenz abar h) l) n =
      (fderiv ℝ (fun a => approxInverse.action (F_coeffs a) l n) abar) h :=
  fderiv_G_lorenz_coeff_at abar h l n

/-- Differentiability of `F_coeffs · j k` for finite modes (each mode is polynomial in coordinates). -/
lemma differentiable_F_coeffs (j : Fin L) (k : Fin (N + 1)) :
    Differentiable ℝ (fun a : XL1 ν_val L => F_coeffs a j k) := by
  simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
  cases (k : ℕ) with
  | zero =>
    exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
      (differentiable_pi_apply j)).sub (differentiable_const _)
  | succ n =>
    exact (differentiable_const _ |>.mul
      ((l1Weighted.toSeq_CLM (n + 1)).differentiable.comp
        (differentiable_pi_apply j))).sub
      ((l1Weighted.toSeq_CLM n).differentiable.comp
        (differentiable_φ_lorenz_component j))

/-- Differentiability of `F_coeffs · j k` for all modes (extends `differentiable_F_coeffs`). -/
lemma differentiable_F_coeffs_general (j : Fin L) (k : ℕ) :
    Differentiable ℝ (fun a : XL1 ν_val L => F_coeffs a j k) := by
  simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
  cases k with
  | zero =>
    exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
      (differentiable_pi_apply j)).sub (differentiable_const _)
  | succ n =>
    exact (differentiable_const _ |>.mul
      ((l1Weighted.toSeq_CLM (n + 1)).differentiable.comp
        (differentiable_pi_apply j))).sub
      ((l1Weighted.toSeq_CLM n).differentiable.comp
        (differentiable_φ_lorenz_component j))

/-- Fderiv difference of F_coeffs at two points: only the φ-fderiv difference survives.
The linear part `(k+1) * toSeq(a j)(k+1)` has constant fderiv (cancels in difference). -/
lemma fderiv_F_coeffs_diff (c h : XL1 ν_val L) (j : Fin L) (k : ℕ) :
    (fderiv ℝ (fun a => F_coeffs a j k) c) h -
      (fderiv ℝ (fun a => F_coeffs a j k) abar) h =
      if k = 0 then 0
      else -(l1Weighted.toSeq ((fderiv ℝ (fun x => φ_lorenz x j) c -
              fderiv ℝ (fun x => φ_lorenz x j) abar) h) (k - 1)) := by
  cases k with
  | zero =>
    simp only [ite_true]
    -- F · j 0 = toSeq(a j) 0 - x₀ j, affine → constant fderiv → difference = 0
    have hfn : (fun a : XL1 ν_val L => F_coeffs a j 0) =
        (fun a => l1Weighted.toSeq (a j) 0 - x₀ j) :=
      funext fun a => by simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
    simp_rw [hfn]
    -- fderiv of (CLM - const) = CLM (constant in a)
    have hfd : ∀ a : XL1 ν_val L, fderiv ℝ
        (fun a : XL1 ν_val L => l1Weighted.toSeq (a j) 0 - x₀ j) a =
        (l1Weighted.toSeq_CLM (ν := ν_val) 0).comp (proj_L j) := by
      intro a
      have h1 := ((l1Weighted.toSeq_CLM (ν := ν_val) 0).comp (proj_L j)).hasFDerivAt (x := a)
      have h2 := hasFDerivAt_const (𝕜 := ℝ) (x₀ j) a
      have hfeq : (fun a : XL1 ν_val L => l1Weighted.toSeq (a j) 0 - x₀ j) =
          (⇑((l1Weighted.toSeq_CLM (ν := ν_val) 0).comp (proj_L j)) - fun _ => x₀ j) := rfl
      rw [hfeq, (h1.sub h2).fderiv]; simp
    rw [hfd, hfd, sub_self]
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    have hd_sub : ∀ a : XL1 ν_val L,
        (fderiv ℝ (fun x => F_coeffs x j (n + 1)) a) h =
          ((n : ℝ) + 1) * l1Weighted.toSeq (h j) (n + 1) -
            l1Weighted.toSeq ((fderiv ℝ (fun x => φ_lorenz x j) a) h) n := by
      intro a
      have hfn : (fun x : XL1 ν_val L => F_coeffs x j (n + 1)) =
          (fun x => ((n : ℝ) + 1) * l1Weighted.toSeq (x j) (n + 1) -
            l1Weighted.toSeq (φ_lorenz x j) n) :=
        funext fun x => by simp only [F_coeffs, F_lorenz, l1Omega.mk_apply]
      have hfd : HasFDerivAt (fun x : XL1 ν_val L => F_coeffs x j (n + 1))
          (((n : ℝ) + 1) • ((l1Weighted.toSeq_CLM (ν := ν_val) (n + 1)).comp (proj_L j)) -
            (l1Weighted.toSeq_CLM (ν := ν_val) n).comp
              (fderiv ℝ (fun x => φ_lorenz x j) a)) a := by
        rw [hfn]; exact
          (((l1Weighted.toSeq_CLM (n + 1)).comp (proj_L j)).hasFDerivAt.const_mul
            ((n : ℝ) + 1)).sub
          ((l1Weighted.toSeq_CLM n).hasFDerivAt.comp a
            (differentiable_φ_lorenz_component j a).hasFDerivAt)
      rw [hfd.fderiv]; rfl
    rw [hd_sub c, hd_sub abar]
    simp only [ContinuousLinearMap.sub_apply, lpWeighted.sub_toSeq]; ring

/-- ℚ Jacobian of φ_lorenz at ābar: ∂(φ_j(ā)_n)/∂(a_m_p). -/
private def Dφ_jacobian_Q (j : Fin L) (n : ℕ) (m : Fin L) (p : Fin (N + 1)) : ℚ :=
  match j with
  | 0 => (10 : ℚ) * ((if m.val = 1 then 1 else 0) - (if m.val = 0 then 1 else 0)) *
    (if p.val = n then 1 else 0)
  | 1 => ((28 : ℚ) * (if m.val = 0 then 1 else 0) - (if m.val = 1 then 1 else 0)) *
    (if p.val = n then 1 else 0)
    - (if m.val = 0 ∧ p.val ≤ n then (abar_Q 2).getD (n - p.val) 0 else 0)
    - (if m.val = 2 ∧ p.val ≤ n then (abar_Q 0).getD (n - p.val) 0 else 0)
  | 2 => -((8 / 3 : ℚ) * (if m.val = 2 then 1 else 0) * (if p.val = n then 1 else 0))
    + (if m.val = 0 ∧ p.val ≤ n then (abar_Q 1).getD (n - p.val) 0 else 0)
    + (if m.val = 1 ∧ p.val ≤ n then (abar_Q 0).getD (n - p.val) 0 else 0)

/-- Expected DF matrix entries from the F_coeffs Jacobian formula. -/
private def DF_expected_Q (j m : Fin L) (k p : Fin (N + 1)) : ℚ :=
  match (k : ℕ) with
  | 0 => if j = m ∧ (p : ℕ) = 0 then 1 else 0
  | Nat.succ n =>
    (if j = m ∧ (p : ℕ) = n + 1 then (n : ℚ) + 1 else 0) -
      Dφ_jacobian_Q j n m p

/-- Numerical verification: DF_col entries match the expected Jacobian formula. -/
private lemma DF_col_matches_expected :
    ∀ j m : Fin L, ∀ k p : Fin (N + 1),
      (DF_col j m (p : ℕ)).getD (k : ℕ) 0 = DF_expected_Q j m k p := by
  native_decide

/-- DF correctness: fderiv of F_coeffs matches approxDeriv finite block action.
Step 1: fderiv matches DF_expected_Q analytically.
Step 2: DF_expected_Q = DF_col numerically (native_decide). -/
lemma fderiv_F_coeffs_eq (h : XL1 ν_val L) (j : Fin L) (k : Fin (N + 1)) :
    (fderiv ℝ (fun a => F_coeffs a j k) abar) h =
      ∑ m : Fin L, (approxDeriv.finBlock j m).mulVec
        (fun p => toCoeff (ν := ν_val) h m p) k := by
  -- Rewrite RHS using verified numerical formula
  conv_rhs =>
    simp only [approxDeriv, DF_finBlock, Matrix.mulVec, dotProduct]
    simp only [DF_col_matches_expected j _ k]
  -- LHS: compute fderiv of F_coeffs by cases on k
  revert k; intro ⟨k, hk⟩
  cases k with
  | zero =>
    -- F_coeffs a j 0 = toSeq(a j) 0 - x₀ j (affine → fderiv = coordinate)
    show (fderiv ℝ (fun a : XL1 ν_val L => F_coeffs a j (⟨0, hk⟩ : Fin (N+1))) abar) h = _
    -- F_coeffs a j 0 = toSeq(a j) 0 - x₀ j; fderiv = toCoeff(h,j,0)
    have hfn : ∀ a : XL1 ν_val L, F_coeffs a j (⟨0, hk⟩ : Fin (N+1)) =
        l1Weighted.toSeq (a j) 0 - x₀ j := fun a => rfl
    conv_lhs => rw [show (fun a : XL1 ν_val L => F_coeffs a j (⟨0, hk⟩ : Fin (N+1))) =
      fun a => l1Weighted.toSeq (a j) 0 - x₀ j from funext hfn]
    -- fderiv of (f - const) = fderiv of f = CLM
    rw [fderiv_sub_const, show (fun a : XL1 ν_val L => l1Weighted.toSeq (a j) 0) =
      ⇑((l1Weighted.toSeq_CLM (ν := ν_val) 0).comp (proj_L j)) from rfl,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
      proj_L, ContinuousLinearMap.proj_apply]
    -- RHS is a Kronecker delta sum that collapses to toSeq(h j) 0
    simp only [DF_expected_Q, Fin.val_zero]
    simp only [show ∀ (m : Fin L) (p : Fin (N+1)),
      (if j = m ∧ (p : ℕ) = 0 then (1 : ℚ) else 0) =
        (if j = m then 1 else 0) * (if (p : ℕ) = 0 then 1 else 0) from
      fun m p => by split_ifs <;> simp_all]
    -- Collapse Kronecker delta sum to single term (j, 0)
    change lpWeighted.toSeq (h j) 0 = _
    rw [Finset.sum_eq_single j
      (fun m _ hm => Finset.sum_eq_zero fun p _ => by
        simp [DF_expected_Q, Ne.symm hm])
      (by simp),
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (N + 1))
      (fun p _ hp => by simp [DF_expected_Q, Fin.ext_iff.not.mp hp])
      (by simp)]
    simp [DF_expected_Q, toCoeff]
  | succ n =>
    -- F_coeffs a j (n+1) = (n+1)*toSeq(a j)(n+1) - toSeq(φ(a) j) n
    show (fderiv ℝ (fun a : XL1 ν_val L => F_coeffs a j (⟨n + 1, hk⟩ : Fin (N + 1))) abar) h = _
    conv_lhs => rw [show (fun a : XL1 ν_val L => F_coeffs a j (⟨n + 1, hk⟩ : Fin (N + 1))) =
      fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1) -
        l1Weighted.toSeq (φ_lorenz a j) n from funext fun a => rfl]
    -- fderiv: (n+1)*toCoeff(h,j,n+1) - toSeq(Dφ_lorenz h j) n
    have hd1 : HasFDerivAt (fun a : XL1 ν_val L => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1))
        (((n : ℝ) + 1) • ((l1Weighted.toSeq_CLM (n + 1)).comp (proj_L j))) abar :=
      (((l1Weighted.toSeq_CLM (ν := ν_val) (n + 1)).comp (proj_L j)).hasFDerivAt).const_mul _
    have hd2 : HasFDerivAt (fun a : XL1 ν_val L => l1Weighted.toSeq (φ_lorenz a j) n)
        ((l1Weighted.toSeq_CLM (ν := ν_val) n).comp
          (fderiv ℝ (fun a => φ_lorenz a j) abar)) abar := by
      have := ((l1Weighted.toSeq_CLM (ν := ν_val) n).hasFDerivAt (x := φ_lorenz abar j)).comp abar
        (differentiable_φ_lorenz_component j abar).hasFDerivAt
      convert this using 1
    rw [show (fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1) -
        l1Weighted.toSeq (φ_lorenz a j) n) =
      (fun a => ((n : ℝ) + 1) * l1Weighted.toSeq (a j) (n + 1)) -
        (fun a => l1Weighted.toSeq (φ_lorenz a j) n) from rfl,
      (hd1.sub hd2).fderiv, ContinuousLinearMap.sub_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.fderiv, smul_eq_mul, proj_L, ContinuousLinearMap.proj_apply]
    -- LHS = (n+1)*toCoeff(h,j,n+1) - toSeq(Dφ_lorenz h j) n
    rw [← Dφ_lorenz_eq_fderiv h j]
    -- Convert toSeq_CLM applications to toCoeff/toSeq
    change ((n : ℝ) + 1) * toCoeff (ν := ν_val) h j (n + 1) -
      l1Weighted.toSeq (Dφ_lorenz h j) n = _
    -- Suffices to show Dφ_lorenz matches Jacobian sum
    suffices hDφ : l1Weighted.toSeq (Dφ_lorenz h j) n =
        ∑ m : Fin L, ∑ p : Fin (N + 1),
          ↑(Dφ_jacobian_Q j n m p) * toCoeff (ν := ν_val) h m ↑p by
      rw [hDφ]; simp only [DF_expected_Q]
      -- Both sides: (n+1)*c - Σ D*c = Σ ((n+1)*δ - D)*c
      -- Split ℚ cast of subtraction and distribute
      simp only [show ∀ (m : Fin L) (p : Fin (N + 1)),
        (((if j = m ∧ (p : ℕ) = n + 1 then (↑n + 1 : ℚ) else 0) -
          Dφ_jacobian_Q j n m p : ℚ) : ℝ) * toCoeff (ν := ν_val) h m ↑p =
        (if j = m ∧ (p : ℕ) = n + 1 then ((n : ℝ) + 1) * toCoeff (ν := ν_val) h m ↑p else 0) -
        ↑(Dφ_jacobian_Q j n m p) * toCoeff (ν := ν_val) h m ↑p
        from fun m p => by split_ifs <;> simp <;> push_cast <;> ring]
      simp only [Finset.sum_sub_distrib]
      congr 1
      -- Collapse Kronecker: Σ_m Σ_p (if j=m ∧ p=n+1 then (n+1)*c else 0) = (n+1)*c_{j,n+1}
      -- Collapse Kronecker delta double sum using Finset.sum_eq_single
      rw [Finset.sum_eq_single j
        (fun m _ hm => Finset.sum_eq_zero fun p _ => by simp [Ne.symm hm])
        (by simp),
        Finset.sum_eq_single (⟨n + 1, hk⟩ : Fin (N + 1))
        (fun p _ hp => by simp [show (p : ℕ) ≠ n + 1 from fun h => hp (Fin.ext h)])
        (by simp)]
      simp [toCoeff]
    -- Main: toSeq(Dφ_lorenz h j) n = Σ_m Σ_p Dφ_jacobian_Q(j,n,m,p) * toCoeff(h,m,p)
    -- Expand Dφ_lorenz per component, match CauchyProducts with finite sums
    -- Helper: abar toSeq = ℚ getD cast
    have ha : ∀ i k, l1Weighted.toSeq (abar i) k = ↑((abar_Q i).getD k 0) := fun i k =>
      show abar_seq i k = _ from abar_seq_eq_getD i k
    -- Helper: CauchyProduct as Fin sum (for n < N+1, truncation is exact)
    have hcp : ∀ (f g : ℕ → ℝ), CauchyProduct f g n =
        ∑ p : Fin (N + 1), if (p : ℕ) ≤ n then f p * g (n - p) else 0 := by
      intro f g
      rw [CauchyProduct.apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      symm
      rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ n then f k * g (n - k) else 0),
        ← Finset.sum_filter]
      congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    -- Case split on j
    fin_cases j
    · -- j = 0: Dφ₀ = σ*(h₁ - h₀), only δ_{pn} terms (no CauchyProduct)
      show σ_val * (l1Weighted.toSeq (h 1) n - l1Weighted.toSeq (h 0) n) = _
      simp only [Dφ_jacobian_Q, toCoeff]
      -- Collapse inner sums: Dφ_jacobian for j=0 has factor (if p=n then 1 else 0)
      -- so inner sum = single term at p = ⟨n, by omega⟩
      simp_rw [show ∀ (m : Fin L),
        ∑ p : Fin (N + 1), ↑((10 : ℚ) * ((if m.val = 1 then 1 else 0) - (if m.val = 0 then 1 else 0)) *
          (if p.val = n then 1 else 0)) * lpWeighted.toSeq (h m) ↑p =
        (10 : ℝ) * ((if m.val = 1 then 1 else 0) - (if m.val = 0 then 1 else 0)) *
          lpWeighted.toSeq (h m) n
        from fun m => by
          rw [Finset.sum_eq_single (⟨n, by omega⟩ : Fin (N + 1))
            (fun p _ hp => by simp [show (p : ℕ) ≠ n from fun h => hp (Fin.ext h)])
            (by simp)]
          simp only [ite_true]; fin_cases m <;> simp <;> ring]
      -- Expand Fin L sum: fin_cases on the outer sum variable
      conv_rhs => arg 2; ext m; rw [show m.val = (m : ℕ) from rfl]
      rw [show (∑ m : Fin L, _) = _ from Fin.sum_univ_three _]
      unfold σ_val; norm_num; ring
    · -- j = 1: Dφ₁ = ρ*h₀ - h₁ - (ā₀*h₂ + h₀*ā₂)
      show ρ_val * lpWeighted.toSeq (h 0) n - lpWeighted.toSeq (h 1) n -
        (CauchyProduct (lpWeighted.toSeq (abar 0)) (lpWeighted.toSeq (h 2)) n +
         CauchyProduct (lpWeighted.toSeq (h 0)) (lpWeighted.toSeq (abar 2)) n) = _
      simp only [Dφ_jacobian_Q, toCoeff]
      rw [show (∑ m : Fin L, _) = _ from Fin.sum_univ_three _]
      -- Simplify Fin.val comparisons in the expanded sums
      simp only [show (0 : Fin L).val = 0 from rfl, show (1 : Fin L).val = 1 from rfl,
        show (2 : Fin L).val = 2 from rfl,
        show (0:ℕ) = 1 ↔ False from by decide, show (0:ℕ) = 2 ↔ False from by decide,
        show (1:ℕ) = 0 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide,
        show (2:ℕ) = 0 ↔ False from by decide, show (2:ℕ) = 1 ↔ False from by decide,
        ite_true, ite_false, true_and, false_and, and_true, and_false,
        mul_one, mul_zero, sub_zero, zero_sub, zero_mul, neg_zero, add_zero, zero_add]
      -- m=1 sum: δ collapse → -h₁(n)
      have hm1 : ∑ x : Fin (N + 1), ↑((-1 : ℚ) * if (↑x : ℕ) = n then 1 else 0) *
          lpWeighted.toSeq (h 1) ↑x = -lpWeighted.toSeq (h 1) n := by
        rw [Finset.sum_eq_single ⟨n, by omega⟩
          (fun p _ hp => by
            have : (↑p : ℕ) ≠ n := fun h => hp (Fin.ext h); simp [this])
          (by simp)]
        simp
      -- m=2 sum: → -CauchyProduct(abar 0)(h 2)
      have hm2 : ∑ x : Fin (N + 1),
          ↑(-(if (↑x : ℕ) ≤ n then (abar_Q 0).getD (n - ↑x) 0 else (0 : ℚ))) *
          lpWeighted.toSeq (h 2) ↑x =
          -CauchyProduct (lpWeighted.toSeq (abar 0)) (lpWeighted.toSeq (h 2)) n := by
        simp_rw [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
        rw [congr_fun (CauchyProduct.comm (lpWeighted.toSeq (abar 0))
          (lpWeighted.toSeq (h 2))) n, hcp]
        congr 1; apply Finset.sum_congr rfl; intro x _
        simp only [ha]; split_ifs <;> simp [mul_comm]
      -- m=0 sum: split δ + CP → 28*h₀(n) - CauchyProduct(h 0)(abar 2)
      have hm0 : ∑ x : Fin (N + 1),
          ↑(28 * (if (↑x : ℕ) = n then (1 : ℚ) else 0) -
            (if (↑x : ℕ) ≤ n then (abar_Q 2).getD (n - ↑x) 0 else 0)) *
          lpWeighted.toSeq (h 0) ↑x =
          28 * lpWeighted.toSeq (h 0) n -
          CauchyProduct (lpWeighted.toSeq (h 0)) (lpWeighted.toSeq (abar 2)) n := by
        simp_rw [Rat.cast_sub, sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        · rw [Finset.sum_eq_single ⟨n, by omega⟩
            (fun p _ hp => by
              have : (↑p : ℕ) ≠ n := fun h => hp (Fin.ext h); simp [this])
            (by simp)]
          simp
        · rw [hcp]; apply Finset.sum_congr rfl; intro x _
          simp only [ha]; split_ifs <;> simp [mul_comm]
      rw [hm0, hm1, hm2]; unfold ρ_val; ring
    · -- j = 2: Dφ₂ = -β*h₂ + (ā₀*h₁ + h₀*ā₁)
      show -(β_val * lpWeighted.toSeq (h 2) n) +
        (CauchyProduct (lpWeighted.toSeq (abar 0)) (lpWeighted.toSeq (h 1)) n +
         CauchyProduct (lpWeighted.toSeq (h 0)) (lpWeighted.toSeq (abar 1)) n) = _
      simp only [Dφ_jacobian_Q, toCoeff]
      rw [show (∑ m : Fin L, _) = _ from Fin.sum_univ_three _]
      simp only [show (0 : Fin L).val = 0 from rfl, show (1 : Fin L).val = 1 from rfl,
        show (2 : Fin L).val = 2 from rfl,
        show (0:ℕ) = 1 ↔ False from by decide, show (0:ℕ) = 2 ↔ False from by decide,
        show (1:ℕ) = 0 ↔ False from by decide, show (1:ℕ) = 2 ↔ False from by decide,
        show (2:ℕ) = 0 ↔ False from by decide, show (2:ℕ) = 1 ↔ False from by decide,
        ite_true, ite_false, true_and, false_and, and_true, and_false,
        mul_one, mul_zero, sub_zero, zero_sub, zero_mul, neg_zero, add_zero, zero_add]
      -- m=2 sum: δ collapse → -β_val * h₂(n)
      have hm2 : ∑ x : Fin (N + 1), ↑(-(8 / 3 * if (↑x : ℕ) = n then (1 : ℚ) else 0)) *
          lpWeighted.toSeq (h 2) ↑x = -(β_val * lpWeighted.toSeq (h 2) n) := by
        rw [Finset.sum_eq_single ⟨n, by omega⟩
          (fun p _ hp => by
            have : (↑p : ℕ) ≠ n := fun h => hp (Fin.ext h); simp [this])
          (fun h => absurd (Finset.mem_univ _) h)]
        simp only [Fin.val_mk, ite_true]; unfold β_val; push_cast; ring
      -- m=0 sum: → CauchyProduct(h 0)(abar 1)
      have hm0 : ∑ x : Fin (N + 1),
          ↑(if (↑x : ℕ) ≤ n then (abar_Q 1).getD (n - ↑x) 0 else (0 : ℚ)) *
          lpWeighted.toSeq (h 0) ↑x =
          CauchyProduct (lpWeighted.toSeq (h 0)) (lpWeighted.toSeq (abar 1)) n := by
        rw [hcp]; apply Finset.sum_congr rfl; intro x _
        simp only [ha]; split_ifs <;> simp [mul_comm]
      -- m=1 sum: → CauchyProduct(abar 0)(h 1)
      have hm1 : ∑ x : Fin (N + 1),
          ↑(if (↑x : ℕ) ≤ n then (abar_Q 0).getD (n - ↑x) 0 else (0 : ℚ)) *
          lpWeighted.toSeq (h 1) ↑x =
          CauchyProduct (lpWeighted.toSeq (abar 0)) (lpWeighted.toSeq (h 1)) n := by
        rw [congr_fun (CauchyProduct.comm (lpWeighted.toSeq (abar 0))
          (lpWeighted.toSeq (h 1))) n, hcp]
        apply Finset.sum_congr rfl; intro x _
        simp only [ha]; split_ifs <;> simp [mul_comm]
      rw [hm0, hm1, hm2]; linarith

/-- Z₁ finite-mode identity: composedApprox = fderiv G on modes ≤ N.
Uses `fderiv_action_fin` + `blockFinite_mulVec_assoc` + DF correctness. -/
lemma composedApprox_eq_fderiv_G_fin (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν_val) (composedApprox.toCLM (ν := ν_val) h) l n =
      toCoeff (ν := ν_val) ((fderiv ℝ G_lorenz abar) h) l n := by
  -- LHS: composedApprox.action(toCoeff h) l n
  rw [SystemBlockDiagData.toCoeff_toCLM]
  -- RHS: fderiv(a ↦ A.action(F a) l n)(abar)(h) via chain rule
  show composedApprox.action (toCoeff (ν := ν_val) h) l n =
    l1Weighted.toSeq ((fderiv ℝ G_lorenz abar h) l) n
  rw [fderiv_G_lorenz_coeff h l n]
  -- fderiv_action_fin: RHS = A.action(fderiv_F_coeffs) l n
  rw [approxInverse.fderiv_action_fin F_coeffs differentiable_F_coeffs l n hn abar h]
  -- Both sides expand to same finite double sum via block matrix associativity
  set n' : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  -- LHS: expand composedApprox.action with finBlock = A·DF (matrix product)
  rw [SystemBlockDiagData.action_fin_eq_sum_mulVec composedApprox _ l n']
  simp only [composedApprox]
  -- Apply blockFinite_mulVec_assoc to factor A out (via congr_fun at index n')
  have hassoc := congr_fun (blockFinite_mulVec_assoc approxInverse.finBlock approxDeriv.finBlock
    (fun j k => toCoeff (ν := ν_val) h j ↑k) l) n'
  -- hassoc: LHS_assoc n' = RHS_assoc n', convert goal LHS to match hassoc RHS
  conv_lhs => rw [show (∑ x, (∑ m, approxInverse.finBlock l m * approxDeriv.finBlock m x).mulVec
    (fun k => toCoeff (ν := ν_val) h x ↑k) n') =
    (∑ x, (∑ m, approxInverse.finBlock l m * approxDeriv.finBlock m x).mulVec
      (fun k => toCoeff (ν := ν_val) h x ↑k)) n' from (Finset.sum_apply _ _ _).symm]
  rw [← hassoc]
  -- RHS: expand approxInverse.action
  rw [SystemBlockDiagData.action_fin_eq_sum_mulVec approxInverse _ l n']
  -- Now LHS = ∑_j A.finBlock l j ×ᵥ (∑_m DF ×ᵥ toCoeff h m)
  -- RHS = ∑_m A.finBlock l m ×ᵥ fderiv_F_coeffs(m)
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  congr 1; ext m; congr 1; ext p; congr 1
  exact (fderiv_F_coeffs_eq h m p).symm

/-- Z₀ bound via preassembled pipeline:
`‖I - composedApprox.toCLM‖ = ‖defect.toCLM‖ ≤ finBlockMatrixNorm(defect) + 0`.
Since defect has tailBound = 0 (tail cancellation), the bound is purely from finite block norms. -/
lemma Z₀_le {Z₀ : ℝ} (hZ₀ : finiteBlockMatrixNorm ν_val defect.finBlock ≤ Z₀) :
    Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ Z₀ := by
  show ‖ContinuousLinearMap.id ℝ _ - composedApprox.toCLM (ν := ν_val)‖ ≤ _
  rw [composedApprox_defect_eq]
  -- ‖defect.toCLM‖ ≤ finBlockMatrixNorm + tailBound = finBlockMatrixNorm + 0
  exact (defect.norm_toCLM_le (ν := ν_val)).trans
    (by simp [defect, defectOfBlockDiagOp, add_zero]; exact hZ₀)

/-- Z₁ bound: `‖composedApprox.toCLM - fderiv G ā‖ ≤ Z₁_bound`.
The difference kills finite modes (both agree on finite block) and on tail mode n > N
equals `shiftDivN(Dφ_l(ā)(h))_n`. Bounded via `shiftDivN_tailTsum_le_div` + ‖Dφ_l(ā)‖. -/
lemma Z₁_le {Z₁ : ℝ} (hZ₁ : 0 ≤ Z₁)
    (htail_bound : ∀ h : XL1 ν_val L, ∀ l : Fin L,
      ‖((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l‖ ≤ Z₁ * ‖h‖) :
    Z₁_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ Z₁ := by
  show ‖(ContinuousLinearMap.id ℝ _).comp (composedApprox.toCLM (ν := ν_val) -
    fderiv ℝ G_lorenz abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  exact norm_le_of_pi_component_bound _ hZ₁ htail_bound

/-! ## 11. Main Theorem Skeleton

With f = G_lorenz, A = id, A† = composedApprox.toCLM:
- Y₀ = ‖G_lorenz(ābar)‖
- Z₀ = ‖I - composedApprox.toCLM‖ = ‖defect.toCLM‖   (finite block norms)
- Z₁ = ‖composedApprox.toCLM - fderiv G ā‖             (tail shiftDivN∘Dφ error)
- Z₂(r) = sup_{c ∈ ball} ‖fderiv G c - fderiv G ā‖ * r  (quadratic Lorenz → linear in r)
-/

/-- Main existence/uniqueness theorem for the Lorenz IVP (Section 8.3).
Uses `general_radii_polynomial_theorem` with `f = G_lorenz`, `A = id`,
`A† = composedApprox.toCLM`. -/
theorem existsUnique
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ Y₀)
    (hZ₀ : Z₀_norm (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ Z₀)
    (hZ₁ : Z₁_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ Z₁)
    (hZ₂ : ∀ c_val ∈ Metric.closedBall (abar : XL1 ν_val L) r₀,
      Z₂_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c_val ≤ Z₂ r₀ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall (abar : XL1 ν_val L) r₀,
      G_lorenz xTilde = 0 := by
  exact general_radii_polynomial_theorem hr₀ hY₀ hZ₀ hZ₁ hZ₂
    differentiable_G_lorenz h_radii Function.injective_id

end Example83

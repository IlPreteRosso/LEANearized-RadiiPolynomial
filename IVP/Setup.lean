import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Concrete
import RadiiPolynomial.SystemTaylorODE.OmegaWeighted

/-!
# Generic IVP Map Infrastructure

Equation-independent definitions and lemmas for IVP zero-finding problems.
Parameterized by a nonlinearity `φ : XL1 ν L → Fin L → l1Weighted ν`.

## The IVP Zero-Finding Problem

Given an ODE system `ẋ = f(x)` with `x(0) = x₀`, the Taylor coefficient
zero-finding map is:
```
  F(a)_l_0     = a_{l,0} - (x₀)_l
  F(a)_l_{k+1} = (k+1) · a_{l,k+1} - φ_l(a)_k
```
where `φ` encodes `f` at the sequence level (Cauchy products for nonlinear terms).

The composed map `G = A ∘ F : XL1 → XL1` (with `A` the approximate inverse) is
the Newton-like map for the radii polynomial theorem.

## What This File Provides (equation-independent)

1. `ivpCoeffs` — the F coefficient formula
2. `ivpMap` — the composed map G = A.action(F)
3. `ivpTail` — the "tail" part: `a - shiftDivN(φ(a))`
4. `ivpFinCorrection` — the finite correction: G - G_tail
5. Decomposition: `ivpMap = ivpTail + ivpFinCorrection`
6. Differentiability (from `φ` differentiability)
7. Fderiv on tail modes

## What Stays Equation-Specific

- `φ` definition (e.g., `φ_lorenz`)
- `differentiable_φ_component` (typically `fun_prop`)
- Fderiv structure of φ (via `auto_poly_fderiv`)
- ℚ mirrors and bridges
-/

open scoped BigOperators Topology
open SystemTaylorODE

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-! ## 1. IVP Coefficient Formula -/

/-- IVP zero-finding coefficients: `F(a)_l_0 = a_0 - x₀`, `F(a)_l_{k+1} = (k+1)a_{k+1} - φ(a)_k`.
Maps into the omega-weighted space (the factor `k+1` is compensated by `ω_k`). -/
def ivpCoeffs (φ : XL1 ν L → Fin L → l1Weighted ν) (x₀ : Fin L → ℝ)
    (a : XL1 ν L) (l : Fin L) (n : ℕ) : ℝ :=
  match n with
  | 0 => l1Weighted.toSeq (a l) 0 - x₀ l
  | n + 1 => ((n : ℝ) + 1) * l1Weighted.toSeq (a l) (n + 1) -
      l1Weighted.toSeq (φ a l) n

/-! ## 2. Composed Map G = A.action(ivpCoeffs) -/

/-- The composed map G = A ∘ F : XL1 → XL1.
Defined at the coefficient level: `A.action` applied to `ivpCoeffs`.
The caller provides `hmem` proving ℓ¹_ν membership of each component.

In practice, `hmem` follows from the tail structure: when `A.tailDiag = 1/n`,
the tail term `(1/n)((n)a_n - φ_{n-1}) = a_n - φ_{n-1}/n` is ℓ¹_ν-summable.
This is equation-specific (depends on the tail structure of A). -/
def ivpMap (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      lpWeighted.Mem ν 1 (A.action (ivpCoeffs φ x₀ a) l))
    (a : XL1 ν L) : XL1 ν L := fun l =>
  lpWeighted.mk (A.action (ivpCoeffs φ x₀ a) l) (hmem a l)

/-- G at the coefficient level. -/
lemma ivpMap_coeff (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      lpWeighted.Mem ν 1 (A.action (ivpCoeffs φ x₀ a) l))
    (a : XL1 ν L) (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (ivpMap A φ x₀ hmem a l) n =
      A.action (ivpCoeffs φ x₀ a) l n := by
  simp [ivpMap, lpWeighted.mk]

/-! ## 3. Tail Decomposition -/

/-- The "tail" part of G: `a l - shiftDivN_CLM(φ(a) l)`.
On modes n > N, this equals G exactly (up to the finite block structure of A).
Manifestly differentiable when φ is differentiable. -/
def ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (a : XL1 ν L) : XL1 ν L := fun l =>
  a l - shiftDivN_CLM (φ a l)

lemma differentiable_ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l)) :
    Differentiable ℝ (ivpTail φ) := by
  intro a; apply differentiableAt_pi.mpr; intro l
  show DifferentiableAt ℝ (fun a : XL1 ν L => a l - shiftDivN_CLM (φ a l)) a
  have h1 : DifferentiableAt ℝ (fun a : XL1 ν L => a l) a :=
    differentiableAt_pi.mp differentiableAt_id l
  have h2 : DifferentiableAt ℝ (fun a : XL1 ν L => shiftDivN_CLM (φ a l)) a :=
    shiftDivN_CLM.differentiableAt.comp a (hφ l a)
  exact h1.sub h2

/-! ## 4. Fderiv on Tail Modes -/

/-- Fderiv of ivpTail at `ā` applied to `h`:
`(fderiv(ivpTail)(ā)(h)) l = h l - shiftDivN_CLM((fderiv(φ·l)(ā))(h))`.
Used for Z₁ bound (tail difference = shiftDivN of Dφ). -/
lemma fderiv_ivpTail (φ : XL1 ν L → Fin L → l1Weighted ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (ā h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ (ivpTail φ) ā h) l =
      h l - shiftDivN_CLM ((fderiv ℝ (fun a => φ a l) ā) h) := by
  have hd : HasFDerivAt (fun a : XL1 ν L => (ivpTail φ a) l)
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin L => l1Weighted ν) l -
       shiftDivN_CLM.comp (fderiv ℝ (fun a => φ a l) ā)) ā := by
    show HasFDerivAt ((fun a : XL1 ν L => a l) - fun a => shiftDivN_CLM (φ a l)) _ ā
    exact ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin L => l1Weighted ν) l).hasFDerivAt).sub
      (shiftDivN_CLM.hasFDerivAt.comp ā (hφ l ā).hasFDerivAt)
  rw [show (fderiv ℝ (ivpTail φ) ā h) l =
      (fderiv ℝ (fun a => (ivpTail φ a) l) ā) h from by
    rw [fderiv_pi (fun i => differentiableAt_pi.mp
      (differentiable_ivpTail φ hφ ā) i)]; rfl]
  rw [hd.fderiv]; simp [ivpTail]

/-! ## 5. Generic Z₁ Tail Bound

For the Z₁ bound, the difference `composedApprox.toCLM - fderiv G ā` satisfies:
- On finite modes (n ≤ N): zero (by construction of composedApprox)
- On tail modes (n > N): equals `shiftDivN_CLM(Dφ(h) l)` (since composedApprox tail = id)

The per-component norm is then bounded by `ν/(N+1) * ‖Dφ(h) l‖` via `shiftDivN_tailTsum_le_div`.

This section provides the generic Z₁ component bound, parameterized by:
- `hfin`: finite modes agree (equation-specific, from composedApprox construction)
- `htail_diff`: tail difference = shiftDivN(Dφ) (from `fderiv_ivpTail`)
- `hcomp_tail`: composedApprox tail = identity -/

/-- Generic Z₁ per-component bound.
Given that finite modes cancel and the tail difference is `shiftDivN(Dφ(h) l)`,
the component norm is bounded by `ν/(N+1) * ‖Dφ(h) l‖`. -/
lemma Z₁_component_le
    (composedApprox : SystemBlockDiagData L N)
    (G : XL1 ν L → XL1 ν L) (ā : XL1 ν L)
    (Dφ : XL1 ν L → Fin L → l1Weighted ν)
    -- Finite modes: composedApprox = fderiv G on n ≤ N
    (hfin : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n = 0)
    -- Tail: difference = shiftDivN(Dφ)
    (htail : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) n)
    (h : XL1 ν L) (l : Fin L) :
    ‖((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l‖ ≤
      (ν : ℝ) / ((N : ℝ) + 1) * ‖Dφ h l‖ := by
  -- Step 1: finite part = 0 → norm = tail tsum starting at N+1
  rw [l1Weighted.norm_eq_tailTsum_of_fin_zero _ (N + 1)
    (fun n hn => hfin h l n (by omega))]
  -- Step 2: rewrite tail terms using htail
  have htail' : ∀ n, |l1Weighted.toSeq
      (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) (n + (N + 1))| =
      |l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) (n + (N + 1))| :=
    fun n => congrArg (|·|) (htail h l (n + (N + 1)) (by omega))
  simp_rw [htail', shiftDivN_CLM_apply]
  -- Step 3: apply shiftDivN_tailTsum_le_div
  exact shiftDivN_tailTsum_le_div (Dφ h l) N

/-- **Generic Z₁ bound**: `‖composedApprox.toCLM - fderiv G ā‖ ≤ Z₁`.
Chains `Z₁_component_le` with per-component Dφ norm bound.

The caller provides:
- `hfin`: finite modes agree (from composedApprox = fderiv G on n ≤ N)
- `htail`: tail difference = shiftDivN(Dφ)
- `hDφ`: per-component `‖Dφ(h) l‖ ≤ K * ‖h‖`
- `hZ₁`: `ν/(N+1) * K ≤ Z₁` -/
lemma ivp_Z₁_le
    (composedApprox : SystemBlockDiagData L N)
    (G : XL1 ν L → XL1 ν L) (ā : XL1 ν L)
    (Dφ : XL1 ν L → Fin L → l1Weighted ν)
    (hfin : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, n ≤ N →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n = 0)
    (htail : ∀ h : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ, N < n →
      l1Weighted.toSeq (((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l) n =
        l1Weighted.toSeq (shiftDivN_CLM (Dφ h l)) n)
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ : ∀ h : XL1 ν L, ∀ l : Fin L, ‖Dφ h l‖ ≤ K * ‖h‖)
    {Z₁ : ℝ} (hZ₁ : (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁) :
    ‖composedApprox.toCLM (ν := ν) - fderiv ℝ G ā‖ ≤ Z₁ := by
  have hν : (0 : ℝ) ≤ (ν : ℝ) / ((N : ℝ) + 1) := div_nonneg ν.coe_nonneg (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (mul_nonneg hν hK) hZ₁)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (le_trans (mul_nonneg hν hK) hZ₁)
    (norm_nonneg _))).mpr fun l => ?_
  calc ‖((composedApprox.toCLM (ν := ν) - fderiv ℝ G ā) h) l‖
      ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖Dφ h l‖ := Z₁_component_le composedApprox G ā Dφ hfin htail h l
    _ ≤ (ν : ℝ) / ((N : ℝ) + 1) * (K * ‖h‖) := mul_le_mul_of_nonneg_left (hDφ h l) hν
    _ ≤ Z₁ * ‖h‖ := by nlinarith [norm_nonneg h]

/-! ## 6. Generic Y₀ Bound

The Y₀ bound `‖G(ā)‖ ≤ C` reduces to:
1. `G(ā) = A.toCLM(F_abar)` where `F_abar = ofCoeff(ivpCoeffs ā)`
2. `norm_toCLM_apply_le` reduces `‖A.toCLM(F_abar)‖` to per-component finite sums
3. `finsum_bound` closes each component sum

The generic lemma packages step 1 (ivpMap → A.toCLM connection) so the caller
just provides: ℚ bridge, support bound, A data bridges, and per-component bounds. -/

/-- **Generic Y₀ bound**: `‖ivpMap A φ x₀ hmem ā‖ ≤ C`.

Reduces to per-component finite sums of `|A.action(ivpCoeffs ā) l n| * ν^n`,
which the caller closes via `finsum_bound using systemBlockDiagActionEval`.

Takes:
- `S`: support bound for `ivpCoeffs φ x₀ ā` (typically `2*N+1` for degree-2 φ)
- `hsupport`: `ivpCoeffs` vanishes beyond S
- `hmem_coeff`: membership proof for `ofCoeff`
- `hcoeff_eq`: G(ā) = A.action(ivpCoeffs ā) at the sequence level
- `hcomp`: per-component bound (user closes with `finsum_bound`) -/
lemma ivp_Y₀_le
    (A : SystemBlockDiagData L N) (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hmem : ∀ a : XL1 ν L, ∀ l : Fin L,
      lpWeighted.Mem ν 1 (A.action (ivpCoeffs φ x₀ a) l))
    (ā : XL1 ν L) (S : ℕ) (hSN : N ≤ S)
    -- Support bound: ivpCoeffs vanishes beyond S
    (hsupport : ∀ l : Fin L, ∀ n, S < n → ivpCoeffs φ x₀ ā l n = 0)
    {C : ℝ} (hC : 0 ≤ C)
    -- Per-component bound (closed by finsum_bound using systemBlockDiagActionEval)
    (hcomp : ∀ l : Fin L,
      ∑ n ∈ Finset.Icc 0 S,
        |A.action (ivpCoeffs φ x₀ ā) l n| * (ν : ℝ) ^ n ≤ C) :
    ‖ivpMap A φ x₀ hmem ā‖ ≤ C := by
  -- Step 1: ‖G(ā)‖ = sup_l ‖G(ā) l‖ where G(ā) l = lpWeighted.mk(A.action(...))
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun l => ?_
  -- Step 2: ‖G(ā) l‖ = finite sum (support bound from A.toCLM_support)
  rw [l1Weighted.norm_eq_Icc_sum_of_support (ivpMap A φ x₀ hmem ā l) S
    (fun n hn => by
      simp only [ivpMap, lpWeighted.mk_apply]
      rw [SystemBlockDiagData.action_tail _ _ _ _ (by omega : N < n)]
      rw [hsupport l n hn, mul_zero])]
  -- Step 3: rewrite toSeq to A.action
  simp_rw [show ∀ n, lpWeighted.toSeq (ivpMap A φ x₀ hmem ā l) n =
    A.action (ivpCoeffs φ x₀ ā) l n from fun n => by simp [ivpMap, lpWeighted.mk]]
  exact hcomp l

/-! ## 7. Differentiability of IVP Coefficients

Each `ivpCoeffs φ x₀ · j k` is differentiable, and the fderiv difference at two
points yields the shifted Dφ difference pattern:
- k = 0: difference = 0 (affine in a, constant fderiv)
- k = n + 1: difference = −(Dφ_diff l h)_n -/

/-- `ivpCoeffs φ x₀ · j k` is differentiable for all k. -/
lemma differentiable_ivpCoeffs (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (j : Fin L) (k : ℕ) :
    Differentiable ℝ (fun a : XL1 ν L => ivpCoeffs φ x₀ a j k) := by
  simp only [ivpCoeffs]
  cases k with
  | zero =>
    exact ((l1Weighted.toSeq_CLM 0).differentiable.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j).differentiable)).sub (differentiable_const _)
  | succ n =>
    exact (differentiable_const _ |>.mul
      ((l1Weighted.toSeq_CLM (n + 1)).differentiable.comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j).differentiable))).sub
      ((l1Weighted.toSeq_CLM n).differentiable.comp (hφ j))

/-- Fderiv difference of `ivpCoeffs` at two points: only the φ-fderiv difference survives.
The linear part `(k+1) * toSeq(a j)(k+1)` has constant fderiv (cancels in difference). -/
lemma fderiv_ivpCoeffs_diff (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (c ā h : XL1 ν L) (j : Fin L) (k : ℕ) :
    (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j k) c) h -
      (fderiv ℝ (fun a => ivpCoeffs φ x₀ a j k) ā) h =
      if k = 0 then 0
      else -(l1Weighted.toSeq ((fderiv ℝ (fun x => φ x j) c -
              fderiv ℝ (fun x => φ x j) ā) h) (k - 1)) := by
  cases k with
  | zero =>
    simp only [ite_true]
    -- ivpCoeffs · j 0 = toSeq(· j) 0 - x₀ j, affine → constant fderiv
    have hfn : (fun a : XL1 ν L => ivpCoeffs φ x₀ a j 0) =
        (fun a => l1Weighted.toSeq (a j) 0 - x₀ j) :=
      funext fun a => by simp only [ivpCoeffs]
    simp_rw [hfn]
    have hfd : ∀ a : XL1 ν L, fderiv ℝ
        (fun a : XL1 ν L => l1Weighted.toSeq (a j) 0 - x₀ j) a =
        (l1Weighted.toSeq_CLM (ν := ν) 0).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j) := by
      intro a
      have h1 := ((l1Weighted.toSeq_CLM (ν := ν) 0).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j)).hasFDerivAt (x := a)
      have h2 := hasFDerivAt_const (𝕜 := ℝ) (x₀ j) a
      have hfeq : (fun a : XL1 ν L => l1Weighted.toSeq (a j) 0 - x₀ j) =
          (⇑((l1Weighted.toSeq_CLM (ν := ν) 0).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j)) -
            fun _ => x₀ j) := rfl
      rw [hfeq, (h1.sub h2).fderiv]; simp
    rw [hfd, hfd, sub_self]
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    -- F · j (n+1) = (n+1) * toSeq(· j)(n+1) - toSeq(φ · j) n
    -- fderiv = (n+1) * toSeq(h j)(n+1) - toSeq(Dφ(a)(h) j) n
    have hd_sub : ∀ a : XL1 ν L,
        (fderiv ℝ (fun x => ivpCoeffs φ x₀ x j (n + 1)) a) h =
          ((n : ℝ) + 1) * l1Weighted.toSeq (h j) (n + 1) -
            l1Weighted.toSeq ((fderiv ℝ (fun x => φ x j) a) h) n := by
      intro a
      have hfn : (fun x : XL1 ν L => ivpCoeffs φ x₀ x j (n + 1)) =
          fun x => ((n : ℝ) + 1) * l1Weighted.toSeq (x j) (n + 1) -
            l1Weighted.toSeq (φ x j) n := funext fun x => rfl
      have hfd : HasFDerivAt (fun x : XL1 ν L => ivpCoeffs φ x₀ x j (n + 1))
          (((n : ℝ) + 1) • ((l1Weighted.toSeq_CLM (n + 1)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j)) -
            (l1Weighted.toSeq_CLM (ν := ν) n).comp (fderiv ℝ (fun x => φ x j) a)) a := by
        rw [hfn]; exact
          (((l1Weighted.toSeq_CLM (n + 1)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Weighted ν) j)).hasFDerivAt.const_mul
            ((n : ℝ) + 1)).sub
          ((l1Weighted.toSeq_CLM n).hasFDerivAt.comp a (hφ j a).hasFDerivAt)
      rw [hfd.fderiv]; rfl
    rw [hd_sub c, hd_sub ā]
    simp only [ContinuousLinearMap.sub_apply, lpWeighted.sub_toSeq]
    ring

/-! ## 8. Generic Z₂ Bound

The Z₂ bound `‖fderiv G c - fderiv G ā‖ ≤ Z₂ * r` for c ∈ B(ā, r) follows from:
1. **Factorization** (IVP-generic): `fderiv_diff(G)(h) = A.toCLM(w)` where w is the
   shifted Dφ difference
2. **Block norm bound** (universal, Layer 0): `‖A.toCLM(w) l‖ ≤ restricted_norm(l) * ‖w‖`
3. **w norm bound** (IVP-generic): `‖w‖ ≤ C·ν·‖c-ā‖·‖h‖`
4. **Evaluation** (caller): `C·ν·restricted_norm(l) ≤ Z₂_val` via `native_decide` -/

lemma ivp_Z₂_le
    (A : SystemBlockDiagData L N)
    (G : XL1 ν L → XL1 ν L)
    (φ : XL1 ν L → Fin L → l1Weighted ν)
    (x₀ : Fin L → ℝ)
    (ā : XL1 ν L)
    (hG_diff : Differentiable ℝ G)
    (hφ : ∀ l, Differentiable ℝ (fun a : XL1 ν L => φ a l))
    (hG_coeff : ∀ (a : XL1 ν L) (l : Fin L) (n : ℕ),
      l1Weighted.toSeq (G a l) n = A.action (ivpCoeffs φ x₀ a) l n)
    (active : Finset (Fin L))
    (hzero : ∀ (c : XL1 ν L) (h : XL1 ν L) (j : Fin L), j ∉ active →
      (fderiv ℝ (fun x => φ x j) c - fderiv ℝ (fun x => φ x j) ā) h = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hDφ_diff : ∀ (c : XL1 ν L) (h : XL1 ν L) (l : Fin L),
      ‖(fderiv ℝ (fun x => φ x l) c - fderiv ℝ (fun x => φ x l) ā) h‖ ≤
        C * ‖c - ā‖ * ‖h‖)
    {Z₂_val : ℝ} (hZ₂_nn : 0 ≤ Z₂_val)
    (hcomp_le : ∀ l : Fin L,
      C * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
        if l ∈ active then A.tailBound else 0) ≤ Z₂_val)
    {r : ℝ} (c : XL1 ν L) (hc : c ∈ Metric.closedBall ā r) :
    ‖fderiv ℝ G c - fderiv ℝ G ā‖ ≤ Z₂_val * r := by
  have hdist : ‖c - ā‖ ≤ r := hc
  suffices h : ‖fderiv ℝ G c - fderiv ℝ G ā‖ ≤ Z₂_val * ‖c - ā‖ from
    h.trans (mul_le_mul_of_nonneg_left hdist hZ₂_nn)
  set F := ivpCoeffs φ x₀
  have hF_diff : ∀ j k, Differentiable ℝ (fun a : XL1 ν L => F a j k) :=
    fun j k => differentiable_ivpCoeffs φ x₀ hφ j k
  -- Chain rule: toSeq(fderiv G a h l) n = fderiv(A.action(F ·) l n)(a)(h)
  have hchain : ∀ (a h' : XL1 ν L) (l : Fin L) (n : ℕ),
      l1Weighted.toSeq ((fderiv ℝ G a h') l) n =
        (fderiv ℝ (fun a => A.action (F a) l n) a) h' := by
    intro a h' l n
    have hcoeff : (fun x => l1Weighted.toSeq (G x l) n) =
        (fun x => A.action (F x) l n) := funext fun x => hG_coeff x l n
    rw [show (fderiv ℝ G a h') l =
        (fderiv ℝ (fun x : XL1 ν L => G x l) a) h' from by
      rw [fderiv_pi (fun i => differentiableAt_pi.mp (hG_diff a) i)]; rfl]
    show l1Weighted.toSeq_CLM n ((fderiv ℝ (fun x => G x l) a) h') = _
    rw [← ContinuousLinearMap.comp_apply (l1Weighted.toSeq_CLM n),
      ← ContinuousLinearMap.fderiv (l1Weighted.toSeq_CLM (ν := ν) n),
      ← fderiv_comp a (l1Weighted.toSeq_CLM n).differentiableAt
        ((differentiableAt_pi.mp (hG_diff a)) l)]
    show (fderiv ℝ (l1Weighted.toSeq_CLM n ∘ fun x => G x l) a) h' = _
    rw [show (l1Weighted.toSeq_CLM (ν := ν) n ∘ fun x => G x l) =
        fun x => A.action (F x) l n from hcoeff]
  -- opNorm_le_bound
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hZ₂_nn (norm_nonneg _))
  intro h'
  rw [ContinuousLinearMap.sub_apply]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hZ₂_nn
    (norm_nonneg _)) (norm_nonneg _))).mpr fun l => ?_
  -- Construct w: shifted Dφ difference
  have hmem : ∀ j : Fin L, lpWeighted.Mem ν 1
      (fun n => if n = 0 then (0 : ℝ) else
        -lpWeighted.toSeq (((fderiv ℝ (fun x => φ x j) c -
          fderiv ℝ (fun x => φ x j) ā) h')) (n - 1)) := by
    intro j; rw [l1Weighted.mem_iff]
    exact (l1Weighted.summable_shifted_weighted
      ((fderiv ℝ (fun x => φ x j) c -
        fderiv ℝ (fun x => φ x j) ā) h')).of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _))
      (fun n => by split_ifs with h0 <;> simp only [abs_neg, abs_zero, zero_mul, le_refl,
        mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _)])
  set w : XL1 ν L := fun j => lpWeighted.mk _ (hmem j)
  -- Factorization: (diff G h') l = A.toCLM(w) l
  have hseq : ∀ n, lpWeighted.toSeq (fderiv ℝ G c h' l - fderiv ℝ G ā h' l) n =
      lpWeighted.toSeq (A.toCLM (ν := ν) w l) n := by
    intro n
    show l1Weighted.toSeq ((fderiv ℝ G c h') l) n -
      l1Weighted.toSeq ((fderiv ℝ G ā h') l) n =
      l1Weighted.toSeq (A.toCLM (ν := ν) w l) n
    rw [hchain c h' l n, hchain ā h' l n]
    change _ = toCoeff (ν := ν) (A.toCLM (ν := ν) w) l n
    rw [SystemBlockDiagData.toCoeff_toCLM]
    have hcd : ∀ j : Fin L, ∀ k : ℕ,
        (fderiv ℝ (fun a => F a j k) c) h' -
          (fderiv ℝ (fun a => F a j k) ā) h' =
        toCoeff (ν := ν) w j k := by
      intro j k
      rw [fderiv_ivpCoeffs_diff φ x₀ hφ c ā h' j k]
      show _ = lpWeighted.toSeq (w j) k
      simp [w, lpWeighted.mk_apply, lpWeighted.sub_toSeq]
    have hF_diff_fin : ∀ j : Fin L, ∀ k : Fin (N + 1),
        Differentiable ℝ (fun a : XL1 ν L => F a j k) :=
      fun j k => hF_diff j k
    by_cases hn : n ≤ N
    · rw [A.fderiv_action_fin F hF_diff_fin l n hn c h',
        A.fderiv_action_fin F hF_diff_fin l n hn ā h']
      simp only [SystemBlockDiagData.action_finite _ _ _ _ hn,
        ← Finset.sum_sub_distrib, ← mul_sub]
      simp_rw [hcd]
    · push_neg at hn
      have hfn : (fun a => A.action (F a) l n) =
          fun a => A.tailDiag l n * F a l n :=
        funext fun a => SystemBlockDiagData.action_tail _ _ _ _ hn
      rw [hfn]
      have hd : ∀ a : XL1 ν L, HasFDerivAt
          (fun a => A.tailDiag l n * F a l n)
          (A.tailDiag l n • fderiv ℝ (fun a => F a l n) a) a := fun a =>
        (hF_diff l n a).hasFDerivAt.const_mul _
      rw [(hd c).fderiv, (hd ā).fderiv]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_sub]
      rw [hcd, SystemBlockDiagData.action_tail _ _ _ _ hn]
  rw [show ((fderiv ℝ G c h' - fderiv ℝ G ā h') : XL1 ν L) l =
      A.toCLM (ν := ν) w l from by
    show (fderiv ℝ G c h') l - (fderiv ℝ G ā h') l = _
    exact lpWeighted.ext hseq]
  -- w vanishes outside active set
  have hw_zero : ∀ j, j ∉ active → w j = 0 := by
    intro j hj; apply lpWeighted.ext; intro k
    show (if k = 0 then (0 : ℝ) else _) = 0
    split_ifs with h0
    · rfl
    · show -lpWeighted.toSeq ((fderiv ℝ (fun x => φ x j) c -
          fderiv ℝ (fun x => φ x j) ā) h') (k - 1) = 0
      rw [hzero c h' j hj]; simp
  -- ‖w‖ ≤ C * ν * ‖c-ā‖ * ‖h'‖
  have hw_norm : ‖w‖ ≤ C * (ν : ℝ) * ‖c - ā‖ * ‖h'‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hC (PosReal.coe_nonneg _)) (norm_nonneg _)) (norm_nonneg _))).mpr fun j => by
      set dj := ((fderiv ℝ (fun x => φ x j) c -
        fderiv ℝ (fun x => φ x j) ā) h')
      have hnorm_w : ‖w j‖ ≤ (ν : ℝ) * ‖dj‖ := by
        rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
        have hsw := l1Weighted.summable_weighted (w j)
        rw [hsw.tsum_eq_zero_add]
        simp only [show lpWeighted.toSeq (w j) 0 = 0 from lpWeighted.mk_apply _ _ 0 ▸ if_pos rfl,
          abs_zero, zero_mul, zero_add]
        rw [show (fun n => |lpWeighted.toSeq (w j) (n + 1)| * (ν : ℝ) ^ (n + 1)) =
          fun n => (ν : ℝ) * (|lpWeighted.toSeq dj n| * (ν : ℝ) ^ n) from by
          ext n; show |if n + 1 = 0 then 0 else -(lpWeighted.toSeq dj n)| * _ = _
          simp [abs_neg, pow_succ]; ring]
        rw [tsum_mul_left]
      calc ‖w j‖ ≤ (ν : ℝ) * ‖dj‖ := hnorm_w
        _ ≤ (ν : ℝ) * (C * ‖c - ā‖ * ‖h'‖) :=
            mul_le_mul_of_nonneg_left (hDφ_diff c h' j) (PosReal.coe_nonneg _)
        _ = C * ↑ν * ‖c - ā‖ * ‖h'‖ := by ring
  -- Assembly: Layer 0 (norm_toCLM_component_le_restricted) + hw_norm + hcomp_le
  have hfactor_nn : 0 ≤ (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      (if l ∈ active then A.tailBound else 0) :=
    add_nonneg (Finset.sum_nonneg fun j _ => blockEntryNorm_nonneg A.finBlock l j)
      (by split <;> [exact A.tailBound_nonneg_at l; exact le_refl _])
  calc ‖A.toCLM (ν := ν) w l‖
      ≤ ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
          if l ∈ active then A.tailBound else 0) * ‖w‖ :=
        A.norm_toCLM_component_le_restricted w l active hw_zero
    _ ≤ ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
          if l ∈ active then A.tailBound else 0) *
          (C * ↑ν * ‖c - ā‖ * ‖h'‖) :=
        mul_le_mul_of_nonneg_left hw_norm hfactor_nn
    _ = C * ↑ν * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
          if l ∈ active then A.tailBound else 0) *
          ‖c - ā‖ * ‖h'‖ := by ring
    _ ≤ Z₂_val * ‖c - ā‖ * ‖h'‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcomp_le l) (norm_nonneg _))
          (norm_nonneg _)

end IVP

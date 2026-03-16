import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import RadiiPolynomial.SystemTaylorODE.LpOneBanachAlgebra

/-!
# `auto_poly_fderiv` — Automatic differentiation for polynomials

Unified tactic for computing derivatives of polynomial expressions. Handles:
- `fderiv` (first-order Fréchet derivative, any `NormedCommRing`)
- `iteratedDeriv` (arbitrary-order scalar derivative, univariate `𝕜 → F`)
- Both scalar ℝ and Banach algebra `l1Weighted ν`
- Pi-type expressions `fun a => a i` (projections) for system-level derivatives

## Architecture

1. **Main simp**: Mathlib `fderiv_*` + `iteratedDeriv_*` lemma sets, `fun_prop` discharger
   (handles both `DifferentiableAt` and `ContDiffAt` side conditions).
   Includes Banach algebra bridge (`smul_id_eq_leftMul`, `leftMul_nsmul`) — type-safe,
   only fires on `l1Weighted`.
   Includes Pi projection bridge (`fderiv_pi_apply` + `differentiable_pi_apply`) —
   handles `fderiv ℝ (· i)` and compound expressions like `fun a => a 0 - a 1`
   for system-level derivatives on `Fin L → l1Weighted ν`.
2. **Cleanup** (via `first`): tries `ring_nf` (fderiv scalar), then `descFactorial` reduction (iteratedDeriv).
   `first` backtracks on failure, so the two strategies don't interfere.

## Usage

```
auto_poly_fderiv                    -- base
auto_poly_fderiv [extra₁, ...]     -- with additional simp lemmas
```
-/

/-! ## Pi projection bridge

`ContinuousLinearMap.fderiv` won't fire on `fderiv ℝ (fun a => a i) x` because `simp` doesn't
recognize `(· i)` as the coercion of `ContinuousLinearMap.proj i`. This bridge lemma fills the gap.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- `fderiv` of coordinate projection `(· i)` on a non-dependent Pi type `ι → F`. -/
@[simp]
theorem fderiv_pi_apply (i : ι) (x : ι → F) :
    fderiv 𝕜 (fun a : ι → F => a i) x = ContinuousLinearMap.proj i := by
  show fderiv 𝕜 (⇑(ContinuousLinearMap.proj (R := 𝕜) i)) x = _
  exact ContinuousLinearMap.fderiv _

/-- Differentiability of coordinate projection — registered with `fun_prop` so that
`simp (discharger := fun_prop)` can discharge `DifferentiableAt` goals for Pi projections
without stuck metavariables. -/
@[fun_prop]
theorem differentiable_pi_apply (i : ι) :
    Differentiable 𝕜 (fun a : ι → F => a i) :=
  (ContinuousLinearMap.proj i : (ι → F) →L[𝕜] F).differentiable

/-! ## Pi-level Banach algebra bridge

When `auto_poly_fderiv` differentiates `fun a => a i * a j` on a Pi type `ι → l1Weighted ν`,
the product rule yields `a j • proj i + a i • proj j` (Mathlib canonical form).
The existing `smul_id_eq_leftMul` only fires for `a • id`. This bridge converts
`a • proj i → (leftMul a).comp (proj i)` so that the result uses `leftMul` uniformly. -/

@[simp]
lemma SystemTaylorODE.l1Weighted.smul_proj_eq_leftMul_comp_proj
    {ν : PosReal} {ι : Type*} [Fintype ι] (a : SystemTaylorODE.l1Weighted ν) (i : ι) :
    a • (ContinuousLinearMap.proj (R := ℝ) i :
      (ι → SystemTaylorODE.l1Weighted ν) →L[ℝ] SystemTaylorODE.l1Weighted ν) =
    (SystemTaylorODE.l1Weighted.leftMul a).comp (ContinuousLinearMap.proj i) := by
  ext h; simp [SystemTaylorODE.l1Weighted.leftMul_apply, smul_eq_mul]

-- Combined fderiv + iteratedDeriv lemma set with Banach algebra bridge.
-- Unmatched lemmas are harmless (simp skips them).

open Lean.Parser.Tactic in
macro "auto_poly_fderiv" : tactic => `(tactic| (
    simp (discharger := fun_prop) only [
      -- === fderiv rules ===
      -- Identity / constants / linear maps
      fderiv_id', fderiv_const_apply, ContinuousLinearMap.fderiv,
      -- Pi projection (system-level: fderiv (· i) = proj i)
      fderiv_pi_apply,
      -- Additive
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_neg,
      -- Constant offsets
      fderiv_add_const, fderiv_sub_const, fderiv_const_add, fderiv_const_sub,
      -- Multiplication
      fderiv_fun_mul, fderiv_mul_const, fderiv_mul_const', fderiv_const_mul,
      -- Scalar multiplication
      fderiv_fun_const_smul,
      -- Powers
      fderiv_fun_pow, fderiv_pow_ring,
      -- Composition
      fderiv_comp',
      -- === iteratedDeriv rules ===
      -- Base cases / constants
      iteratedDeriv_fun_id, iteratedDeriv_fun_id_zero, iteratedDeriv_const,
      -- Additive
      iteratedDeriv_fun_add, iteratedDeriv_fun_sub, iteratedDeriv_fun_neg,
      -- Constant offsets
      iteratedDeriv_const_add, iteratedDeriv_const_sub,
      -- Multiplication (Leibniz rule)
      iteratedDeriv_fun_mul, iteratedDeriv_const_mul, iteratedDeriv_const_smul,
      -- Powers
      iteratedDeriv_pow, iteratedDeriv_fun_pow_zero,
      -- === Banach algebra bridge (l1Weighted only, harmless for scalar ℝ) ===
      SystemTaylorODE.l1Weighted.smul_id_eq_leftMul,
      SystemTaylorODE.l1Weighted.leftMul_nsmul,
      SystemTaylorODE.l1Weighted.smul_proj_eq_leftMul_comp_proj
    ]
    <;> try first
      | (ring_nf; try simp)                                  -- fderiv cleanup
      | (repeat unfold Nat.descFactorial; push_cast; ring)))                                -- fderiv cleanup

open Lean.Parser.Tactic in
macro "auto_poly_fderiv" "[" extras:simpLemma,* "]" : tactic => `(tactic| (
    simp (discharger := fun_prop) only [
      fderiv_id', fderiv_const_apply, ContinuousLinearMap.fderiv,
      fderiv_pi_apply,
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_neg,
      fderiv_add_const, fderiv_sub_const, fderiv_const_add, fderiv_const_sub,
      fderiv_fun_mul, fderiv_mul_const, fderiv_mul_const', fderiv_const_mul,
      fderiv_fun_const_smul,
      fderiv_fun_pow, fderiv_pow_ring,
      fderiv_comp',
      iteratedDeriv_fun_id, iteratedDeriv_fun_id_zero, iteratedDeriv_const,
      iteratedDeriv_fun_add, iteratedDeriv_fun_sub, iteratedDeriv_fun_neg,
      iteratedDeriv_const_add, iteratedDeriv_const_sub,
      iteratedDeriv_fun_mul, iteratedDeriv_const_mul, iteratedDeriv_const_smul,
      iteratedDeriv_pow, iteratedDeriv_fun_pow_zero,
      SystemTaylorODE.l1Weighted.smul_id_eq_leftMul,
      SystemTaylorODE.l1Weighted.leftMul_nsmul,
      SystemTaylorODE.l1Weighted.smul_proj_eq_leftMul_comp_proj,
      $extras,*
    ]
    <;> try first
      | (repeat unfold Nat.descFactorial; push_cast; ring)
      | (ring_nf; try simp [$extras,*])))

/-! ## Tests -/

section tests

-- fderiv: scalar ℝ, x^2 - c
open ContinuousLinearMap in
example (x c : ℝ) :
    fderiv ℝ (fun y => y ^ 2 - c) x = (2 • x ^ 1) • ContinuousLinearMap.id ℝ ℝ := by
  auto_poly_fderiv

-- fderiv: identity
open ContinuousLinearMap in
example (x : ℝ) :
    fderiv ℝ (fun y : ℝ => y) x = ContinuousLinearMap.id ℝ ℝ := by
  auto_poly_fderiv

-- fderiv: constant
open ContinuousLinearMap in
example (x : ℝ) :
    fderiv ℝ (fun _ : ℝ => (3 : ℝ)) x = 0 := by
  auto_poly_fderiv

-- iteratedDeriv: 2nd derivative of x^3 = 6x
example (x : ℝ) : iteratedDeriv 2 (· ^ 3 : ℝ → ℝ) x = 6 * x := by
  auto_poly_fderiv

-- iteratedDeriv: 2nd derivative of x^2 - c = 2 (Z₂ use case)
example (x c : ℝ) : iteratedDeriv 2 (fun y => y ^ 2 - c) x = 2 := by
  auto_poly_fderiv

-- iteratedDeriv: 3rd derivative of x^4 = 24x
example (x : ℝ) : iteratedDeriv 3 (· ^ 4 : ℝ → ℝ) x = 24 * x := by
  auto_poly_fderiv

-- iteratedDeriv: 1st derivative of x^2 = 2x
example (x : ℝ) : iteratedDeriv 1 (· ^ 2 : ℝ → ℝ) x = 2 * x := by
  auto_poly_fderiv

-- === System-level (Pi type) tests ===

-- fderiv: projection (· i) for Pi type
example (a : Fin 3 → ℝ) :
    fderiv ℝ (fun a : Fin 3 → ℝ => a 0) a = ContinuousLinearMap.proj (0 : Fin 3) := by
  auto_poly_fderiv

-- Test: fun_prop on Pi type differentiability
example (a : Fin 3 → ℝ) : DifferentiableAt ℝ (fun a : Fin 3 → ℝ => a 0 - a 1) a := by
  fun_prop

-- fderiv: Pi subtraction — auto_poly_fderiv handles compound Pi via @[fun_prop] bridge
private abbrev proj₃ (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

example (a : Fin 3 → ℝ) :
    fderiv ℝ (fun a : Fin 3 → ℝ => a 0 - a 1) a = proj₃ 0 - proj₃ 1 := by
  auto_poly_fderiv

-- fderiv: Pi bilinear term a_0 * a_2 on l1Weighted (Banach algebra)
-- Note: fderiv_fun_mul produces c(x)•Dd + d(x)•Dc, so a_0•proj_2 + a_2•proj_0
open SystemTaylorODE in
example {ν : PosReal} (a : Fin 3 → l1Weighted ν) :
    fderiv ℝ (fun a : Fin 3 → l1Weighted ν => a 0 * a 2) a =
    (l1Weighted.leftMul (a 0)).comp (ContinuousLinearMap.proj 2) +
    (l1Weighted.leftMul (a 2)).comp (ContinuousLinearMap.proj 0) := by
  auto_poly_fderiv

end tests

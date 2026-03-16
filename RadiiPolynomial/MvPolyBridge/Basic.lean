import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.SystemTaylorODE.CauchyProduct
import RadiiPolynomial.SystemTaylorODE.LpOneBanachAlgebra

/-!
# MvPolynomial Bridge: Symbolic Specification ↔ Banach Algebra Evaluation

Bridges between `MvPolynomial (Fin L) ℚ` (symbolic polynomial specification)
and `l1Weighted ν` (Banach algebra with CauchyProduct multiplication).

## Architecture

`MvPolynomial` is noncomputable in Mathlib, so it lives in the PROOF world only.
For `native_decide`, the user provides a computable ℚ mirror (`φ_Q : Fin L → ℕ → ℚ`)
as in the existing pipeline. The MvPolynomial bridge automates:

1. **ℚ↔ℝ bridge**: `toSeq(aeval a p) n = (mvPolyCoeffQ p arrs n : ℝ)`
   — reduces to `ratCast_CauchyProduct` + ring hom properties
2. **Differentiability**: `aeval · p` is differentiable (polynomial on Banach algebra)
3. **Fderiv via pderiv**: `fderiv(aeval · p)(a) = Σᵢ leftMul(aeval a (pderiv i p)) ∘ proj i`
4. **DF verification**: Jacobian entries = `mvPolyCoeffQ(pderiv m (φ_spec j))`
5. **Z₂ bound**: for degree ≤ 2, `pderiv i (pderiv j p)` is constant → bilinear bound

The computable ℚ evaluator (`φ_Q`) matches `mvPolyCoeffQ` by a simple
agreement lemma. The user proves this once per equation (~5 lines).

## Key Insight

The value of MvPolynomial is NOT computation — it's PROOF automation.
By stating φ as `MvPolynomial (Fin L) ℚ`, we get:
- `differentiable_aeval` (replaces ~60 lines of manual differentiability proofs)
- `fderiv_aeval` (replaces ~100 lines of fderiv computation)
- `pderiv`-based DF verification (replaces ~200 lines of `fderiv_F_coeffs_eq`)
- degree-based Z₂ bound (replaces ~60 lines of bilinear bound proofs)
-/

open MvPolynomial (C X aeval pderiv)
open SystemTaylorODE

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-! ## 1. Noncomputable ℚ Evaluation via PowerSeries

Used in bridge proofs only (not `native_decide`). -/

/-- Convert ℚ array to PowerSeries ℚ (formal power series with CauchyProduct mul). -/
def arrayToPowerSeries (arr : Array ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => arr.getD n 0

/-- Evaluate MvPolynomial in PowerSeries ℚ. -/
def mvPolyToPowerSeries (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → PowerSeries ℚ) : PowerSeries ℚ :=
  MvPolynomial.eval₂ PowerSeries.C seqs p

/-- The n-th ℚ coefficient of the polynomial evaluation.
Noncomputable; used in bridge proofs connecting the user's computable `φ_Q`
to the ℝ evaluation `aeval`. -/
def mvPolyCoeffQ (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) : ℚ :=
  (PowerSeries.coeff (R := ℚ) n) (mvPolyToPowerSeries p (fun i => arrayToPowerSeries (arrs i)))

/-! ## 2. ℝ Evaluation via aeval into Banach Algebra -/

variable {ν : PosReal}

/-- Algebra ℚ instance for l1Weighted via the chain ℚ →(algebraMap) ℝ →(algebraMap) l1Weighted.
Needed for `MvPolynomial.aeval` to target `l1Weighted ν`. -/
instance l1Weighted.instAlgebraRat : Algebra ℚ (l1Weighted ν) :=
  RingHom.toAlgebra ((algebraMap ℝ (l1Weighted ν)).comp (algebraMap ℚ ℝ))

/-- Evaluate MvPolynomial in the Banach algebra `l1Weighted ν` via `aeval`.
Multiplication = CauchyProduct (from `instNormedCommRing`). -/
def evalInBanach (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) : l1Weighted ν :=
  aeval a p

/-! ## 3. Master Bridge (TODO)

The master bridge theorem connects the three worlds:
- ℝ world: `l1Weighted.toSeq (evalInBanach p a) n`
- ℚ bridge: `(mvPolyCoeffQ p arrs n : ℝ)`
- Computable ℚ: `(φ_Q l n : ℝ)` (user-provided, proven equal to mvPolyCoeffQ)

```
theorem master_bridge (p : MvPolynomial (Fin L) ℚ)
    (a : Fin L → l1Weighted ν) (arrs : Fin L → Array ℚ)
    (ha : ∀ i n, l1Weighted.toSeq (a i) n = ((arrs i).getD n 0 : ℝ))
    (n : ℕ) :
    l1Weighted.toSeq (evalInBanach p a) n = (mvPolyCoeffQ p arrs n : ℝ)
```

Proof strategy: Both `aeval` and `eval₂ PowerSeries.C` are ring homomorphisms.
They agree on generators (constants via algebraMap, variables via `ha`).
By universality, they agree on all polynomials. Then `ratCast_CauchyProduct` bridges
the PowerSeries.coeff to l1Weighted.toSeq. -/

/-! ## 4. POC: Lorenz φ_spec -/

/-- Lorenz nonlinearity as MvPolynomial (ℚ coefficients).
Noncomputable (MvPolynomial.C/X are noncomputable in Mathlib).
Used for proofs only; the computable ℚ mirror is `φ_lorenz_Q` in Certificate.lean.

  φ₀ = σ(a₁ - a₀),  φ₁ = ρa₀ - a₁ - a₀a₂,  φ₂ = -βa₂ + a₀a₁ -/
def φ_lorenz_spec : Fin 3 → MvPolynomial (Fin 3) ℚ
  | 0 => C 10 * (X 1 - X 0)
  | 1 => C 28 * X 0 - X 1 - X 0 * X 2
  | 2 => -(C (8/3) * X 2) + X 0 * X 1

end MvPolyBridge

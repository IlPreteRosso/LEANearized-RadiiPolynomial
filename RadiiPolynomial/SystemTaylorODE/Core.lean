import RadiiPolynomial.SystemTaylorODE.ScaledReal
import RadiiPolynomial.RadiiPolyGeneral

/-!
# SystemTaylorODE Core API (Section 8.2 direction)

Systems-level API for Taylor ODE validation with domain/range spaces,
abstracted over a sequence-space family `Seq : PosReal → Type*`.

- `X = (Seq ν)^L`, modeled as `Fin L → Seq ν`
- `Y = (Seq ν')^L`, modeled as `Fin L → Seq ν'`

Canonical norm quantities (`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`) are
defined over general Banach spaces (`E F : Type*` with `NormedAddCommGroup`),
so both `l1Weighted ν` (scalar) and `XL1 ν L` (system) can use them without
type bridging or `(Seq := Seq)` annotations.

Certificates call `general_radii_polynomial_theorem` directly with these
canonical norm definitions.
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace SystemTaylorODE

variable {Seq : PosReal → Type*}
variable [∀ ν, NormedAddCommGroup (Seq ν)]
variable [∀ ν, NormedSpace ℝ (Seq ν)]
variable [∀ ν, CompleteSpace (Seq ν)]

/-- Domain space `X = (Seq ν)^L` for an `L`-component system.
Ref: §8.2, p.195. -/
abbrev X (Seq : PosReal → Type*) (ν : PosReal) (L : ℕ) := Fin L → Seq ν

/-- Range space `Y = (Seq ν')^L` for an `L`-component system.
Ref: §8.2, p.195 (after (8.15)). -/
abbrev Y (Seq : PosReal → Type*) (ν' : PosReal) (L : ℕ) := Fin L → Seq ν'

/-- Backward-compatible alias when domain and range use the same weight. -/
abbrev Space (Seq : PosReal → Type*) (ν : PosReal) (L : ℕ) := X Seq ν L

section CanonicalBounds

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical `Y₀`: `‖A(f(x̄))‖`.
Ref: (7.30), Thm 7.6.2; cf. Thm 8.2.2 (p.200). -/
def Y₀_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) : ℝ := ‖A (f xBar)‖

/-- Canonical `Z₀`: `‖I - A∘A†‖`.
Ref: (7.31), Thm 7.6.2; aggregated as (8.22), p.200. -/
def Z₀_norm (A : F →L[ℝ] E) (A_dagger : E →L[ℝ] F) : ℝ :=
  ‖ContinuousLinearMap.id ℝ E - A.comp A_dagger‖

/-- Canonical `Z₁`: `‖A∘(A† - Df(x̄))‖`.
Ref: (7.32), Thm 7.6.2; aggregated as (8.23), p.200. -/
def Z₁_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) (A_dagger : E →L[ℝ] F) : ℝ :=
  ‖A.comp (A_dagger - fderiv ℝ f xBar)‖

/-- Canonical `Z₂` at `c`: `‖A∘(Df(c) - Df(x̄))‖`.
Ref: (7.33), Thm 7.6.2; aggregated as (8.24), p.200. -/
def Z₂_norm (f : E → F) (xBar : E) (A : F →L[ℝ] E) (c : E) : ℝ :=
  ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖

end CanonicalBounds


end SystemTaylorODE

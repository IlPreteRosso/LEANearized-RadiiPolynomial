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

Theorem wrappers around `general_radii_polynomial_theorem`. Scalar (`L = 1`)
problems use `ScalarBlockDiagData.existsUnique_of_scalar_bounds` from
`BlockDiagSystem/Scalar.lean` instead of separate scalar types.
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

section TheoremAPI

variable {ν ν' : PosReal} {L : ℕ}
variable {f : X Seq ν L → Y Seq ν' L}
variable {xBar : X Seq ν L}
variable {A : Y Seq ν' L →L[ℝ] X Seq ν L}
variable {A_dagger : X Seq ν L →L[ℝ] Y Seq ν' L}
variable {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}

/-- Systems-level direct wrapper around `general_radii_polynomial_theorem`
for `E = X` and `F = Y`.
Ref: Thm 7.6.2. -/
theorem existsUnique_of_direct_bounds
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm f xBar A ≤ Y₀)
    (hZ₀ : Z₀_norm A A_dagger ≤ Z₀)
    (hZ₁ : Z₁_norm f xBar A A_dagger ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall xBar r₀,
      Z₂_norm f xBar A c ≤ Z₂ r₀ * r₀)
    (hf_diff : Differentiable ℝ f)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (hA_inj : Function.Injective A) :
    ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 := by
  exact general_radii_polynomial_theorem
    (f := f) (xBar := xBar) (A := A) (A_dagger := A_dagger)
    (Y₀ := Y₀) (Z₀ := Z₀) (Z₁ := Z₁) (Z₂ := Z₂) (r₀ := r₀)
    hr₀ hY₀ hZ₀ hZ₁ hZ₂ hf_diff h_radii hA_inj

end TheoremAPI

section ConstantZ2

variable {ν ν' : PosReal} {L : ℕ}
variable {f : X Seq ν L → Y Seq ν' L}
variable {xBar : X Seq ν L}
variable {A : Y Seq ν' L →L[ℝ] X Seq ν L}
variable {A_dagger : X Seq ν L →L[ℝ] Y Seq ν' L}
variable {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}

/-- Constant-`Z₂` variant, matching the common numerical pipeline pattern where
`Z₂(r)` is bounded by a constant on the chosen radius.
Ref: constant-`Z₂` specialization of Thm 7.6.2. -/
theorem existsUnique_of_direct_bounds_constZ₂
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm f xBar A ≤ Y₀)
    (hZ₀ : Z₀_norm A A_dagger ≤ Z₀)
    (hZ₁ : Z₁_norm f xBar A A_dagger ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall xBar r₀,
      Z₂_norm f xBar A c ≤ Z₂ * r₀)
    (hf_diff : Differentiable ℝ f)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (hA_inj : Function.Injective A) :
    ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 := by
  exact existsUnique_of_direct_bounds (Seq := Seq)
    (Y₀ := Y₀) (Z₀ := Z₀) (Z₁ := Z₁) (Z₂ := fun _ => Z₂) (r₀ := r₀)
    hr₀ hY₀ hZ₀ hZ₁ (by simpa using hZ₂) hf_diff h_radii hA_inj

end ConstantZ2

section CertificateAPI

variable {ν ν' : PosReal} {L : ℕ}
variable {f : X Seq ν L → Y Seq ν' L}
variable {xBar : X Seq ν L}
variable {A : Y Seq ν' L →L[ℝ] X Seq ν L}
variable {A_dagger : X Seq ν L →L[ℝ] Y Seq ν' L}
variable {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}

/-- Reusable package for the four direct norm inequalities with constant `Z₂`.
This captures the common numerical stage: prove canonical `Y₀/Z₀/Z₁/Z₂`
inequalities for fixed constants before assembling theorem side-conditions. -/
structure DirectNormBoundsConstZ₂
    (f : X Seq ν L → Y Seq ν' L)
    (xBar : X Seq ν L)
    (A : Y Seq ν' L →L[ℝ] X Seq ν L)
    (A_dagger : X Seq ν L →L[ℝ] Y Seq ν' L)
    (Y₀ Z₀ Z₁ Z₂ r₀ : ℝ) where
  hY₀ : Y₀_norm f xBar A ≤ Y₀
  hZ₀ : Z₀_norm A A_dagger ≤ Z₀
  hZ₁ : Z₁_norm f xBar A A_dagger ≤ Z₁
  hZ₂ : ∀ c ∈ Metric.closedBall xBar r₀,
    Z₂_norm f xBar A c ≤ Z₂ * r₀

/-- Full direct certificate with constant `Z₂`:
norm bounds + `r₀>0` + differentiability + radii negativity + injectivity. -/
structure DirectCertificateConstZ₂
    (f : X Seq ν L → Y Seq ν' L)
    (xBar : X Seq ν L)
    (A : Y Seq ν' L →L[ℝ] X Seq ν L)
    (A_dagger : X Seq ν L →L[ℝ] Y Seq ν' L)
    (Y₀ Z₀ Z₁ Z₂ r₀ : ℝ) where
  bounds :
    DirectNormBoundsConstZ₂ f xBar A A_dagger Y₀ Z₀ Z₁ Z₂ r₀
  hr₀ : 0 < r₀
  hf_diff : Differentiable ℝ f
  h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0
  hA_inj : Function.Injective A

/-- Certificate-driven wrapper: consume `DirectCertificateConstZ₂` directly. -/
theorem DirectCertificateConstZ₂.existsUnique
    (C : DirectCertificateConstZ₂ f xBar A A_dagger Y₀ Z₀ Z₁ Z₂ r₀) :
    ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 := by
  exact existsUnique_of_direct_bounds_constZ₂
    (f := f) (xBar := xBar) (A := A) (A_dagger := A_dagger)
    (Y₀ := Y₀) (Z₀ := Z₀) (Z₁ := Z₁) (Z₂ := Z₂) (r₀ := r₀)
    C.hr₀ C.bounds.hY₀ C.bounds.hZ₀ C.bounds.hZ₁ C.bounds.hZ₂ C.hf_diff C.h_radii C.hA_inj

end CertificateAPI

end SystemTaylorODE

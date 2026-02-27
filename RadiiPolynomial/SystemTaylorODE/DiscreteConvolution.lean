import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Minimal Discrete Convolution API

This file keeps only the additive discrete-convolution pieces currently used by
`SystemTaylorODE.CauchyProduct`:

- `addConvolution`
- `addRingConvolution`
- `addConvolution_eq_sum_antidiagonal`
-/

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M S E E' F R : Type*}

/-- Additive fiber at `x`: all pairs `(a,b)` with `a + b = x`. -/
def addFiber [AddMonoid M] (x : M) : Set (M × M) := {ab | ab.1 + ab.2 = x}

/-- Membership characterization for `addFiber`. -/
lemma mem_addFiber [AddMonoid M] {x : M} {ab : M × M} :
    ab ∈ addFiber x ↔ ab.1 + ab.2 = x := Iff.rfl

/-- Additive discrete convolution with explicit bilinear map:
`(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/
def addConvolution [AddMonoid M] [CommSemiring S]
    [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
    [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for additive discrete convolution. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

/-- Additive ring-multiplication convolution:
`(f ⋆ᵣ₊ g) x = ∑' ab : addFiber x, f ab.1 * g ab.2`. -/
def addRingConvolution [AddMonoid M] [Semiring R] [TopologicalSpace R]
    (f g : M → R) : M → R :=
  addConvolution (S := ℕ) (LinearMap.mul ℕ R) f g

/-- Notation for additive ring convolution. -/
scoped notation:67 f:68 " ⋆ᵣ₊ " g:67 => addRingConvolution f g

section AntidiagonalBridge

variable [AddMonoid M] [Finset.HasAntidiagonal M]
variable [CommSemiring S] [AddCommMonoid E] [Module S E]

/-- The additive fiber equals the finite antidiagonal. -/
private lemma addFiber_eq_antidiagonal (x : M) :
    addFiber x = ↑(Finset.antidiagonal x) := by
  ext ab
  simp [addFiber, Finset.mem_antidiagonal]

variable [AddCommMonoid E'] [Module S E'] [AddCommMonoid F] [Module S F]
variable [TopologicalSpace F]

/-- For `HasAntidiagonal` types, additive convolution equals a finite antidiagonal sum. -/
lemma addConvolution_eq_sum_antidiagonal
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆₊[L] g) x = ∑ ab ∈ Finset.antidiagonal x, L (f ab.1) (g ab.2) := by
  simp [addConvolution]
  rw [addFiber_eq_antidiagonal (M := M) x]
  simpa using (Finset.tsum_subtype' (s := Finset.antidiagonal x)
    (f := fun ab : M × M => L (f ab.1) (g ab.2)))

end AntidiagonalBridge

end DiscreteConvolution

end

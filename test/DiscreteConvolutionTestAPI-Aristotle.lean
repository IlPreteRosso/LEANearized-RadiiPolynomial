/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c97a4363-b1a7-4655-b1ea-1303206c2e3e

The following was proved by Aristotle:

- theorem IsL1.convolution (hf : IsL1 f) (hg : IsL1 g) : IsL1 (f ⋆ g)

- theorem l1Norm_convolution_le (hf : IsL1 f) (hg : IsL1 g) :
    l1Norm (f ⋆ g) ≤ l1Norm f * l1Norm g

- theorem delta_convolution (f : M → R) (hf : ConvolutionExists delta f) :
    delta ⋆ f = f

- theorem convolution_delta (f : M → R) (hf : ConvolutionExists f delta) :
    f ⋆ delta = f

- theorem convolution_comm (f g : M → R)
    (hfg : ConvolutionExists f g) (hgf : ConvolutionExists g f) :
    f ⋆ g = g ⋆ f
-/

/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic


/-!
# Discrete Convolution of Functions

This file defines the discrete convolution on two functions `f g : M → R` where `M` is a monoid:

  `(f ⋆ g) x = ∑' (a, b) : M × M, if a * b = x then f a * g b else 0`

This is analogous to `MeasureTheory.convolution` but for the discrete (counting measure) setting.

## Main Definitions

* `DiscreteConvolution.ConvolutionExistsAt f g x`: the convolution is well-defined at `x`
* `DiscreteConvolution.ConvolutionExists f g`: the convolution is well-defined everywhere
* `DiscreteConvolution.convolution f g x`: the convolution `(f ⋆ g) x`

## Main Results

* `DiscreteConvolution.convolution_assoc`: associativity `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`
* `DiscreteConvolution.one_convolution`: identity `δ₁ ⋆ f = f`
* `DiscreteConvolution.convolution_one`: identity `f ⋆ δ₁ = f`
* `DiscreteConvolution.convolution_comm`: commutativity (for commutative monoids)

## Design Notes

Unlike `MeasureTheory.convolution` which uses `(f ⋆ g) x = ∫ t, f(t) * g(x - t) ∂μ` requiring
a group structure for subtraction, our definition sums over all pairs `(a, b)` with `a * b = x`.
This works for any monoid.

For ℓ¹ functions on a monoid M, the convolution satisfies `‖f ⋆ g‖₁ ≤ ‖f‖₁ · ‖g‖₁`.

## Notation

* `f ⋆ g` for the discrete convolution (scoped in `DiscreteConvolution`)
-/

open scoped BigOperators NNReal ENNReal

open Finset

noncomputable section

namespace DiscreteConvolution

variable {M : Type*} {R : Type*}

/-! ### Multiplication Fiber -/

section Fiber

variable [Monoid M]

/-- The multiplication map `(a, b) ↦ a * b`. -/
@[to_additive /-- The addition map `(a, b) ↦ a + b`. -/]
def mulMap : M × M → M := Function.uncurry (· * ·)

@[to_additive (attr := simp)]
theorem mulMap_apply (ab : M × M) : mulMap ab = ab.1 * ab.2 := rfl

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`. -/]
def mulFiber (x : M) : Set (M × M) := mulMap ⁻¹' {x}

@[to_additive (attr := simp)]
theorem mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := Set.mem_preimage

@[to_additive]
theorem mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := mul_one 1

end Fiber

/-! ### Convolution Existence -/

section Existence

variable [Monoid M] [Semiring R] [TopologicalSpace R]

/-- The convolution of `f` and `g` exists at `x` when the sum over the fiber is summable. -/
def ConvolutionExistsAt (f g : M → R) (x : M) : Prop :=
  Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2

/-- The convolution of `f` and `g` exists when it exists at every point. -/
def ConvolutionExists (f g : M → R) : Prop :=
  ∀ x, ConvolutionExistsAt f g x

end Existence

/-! ### Convolution Definition -/

section Definition

variable [Monoid M] [Semiring R] [TopologicalSpace R]

/-- The discrete convolution of `f` and `g`:
`(f ⋆ g) x = ∑' (a, b) : mulFiber x, f a * g b`. -/
def convolution (f g : M → R) : M → R :=
  fun x => ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2

scoped notation:70 f:70 " ⋆ " g:71 => convolution f g

@[simp]
theorem convolution_apply (f g : M → R) (x : M) :
    (f ⋆ g) x = ∑' ab : mulFiber x, f ab.1.1 * g ab.1.2 := rfl

end Definition

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] [Semiring R]

/-- The identity for convolution: `δ₁(x) = 1` if `x = 1`, else `0`. -/
def delta : M → R := Pi.single 1 1

@[simp]
theorem delta_one : (delta : M → R) 1 = 1 := Pi.single_eq_same 1 1

theorem delta_ne {x : M} (hx : x ≠ 1) : (delta : M → R) x = 0 := Pi.single_eq_of_ne hx 1

end Identity

/-! ### Properties for Normed Rings -/

section NormedRing

variable [Monoid M] [NormedRing R]

variable {f g : M → R}

/-! #### ℓ¹ Membership -/

/-- A function is in ℓ¹ if its norm sum converges. Equivalent to `Memℓp f 1`. -/
def IsL1 (f : M → R) : Prop := Summable fun m => ‖f m‖

omit [Monoid M] in
theorem isL1_iff_memℓp (f : M → R) : IsL1 f ↔ Memℓp f 1 := by
  simp only [IsL1, memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one, Real.rpow_one]

/-- The ℓ¹ norm of a function. -/
def l1Norm (f : M → R) : ℝ := ∑' m, ‖f m‖

omit [Monoid M] in
theorem l1Norm_nonneg (f : M → R) : 0 ≤ l1Norm f :=
  tsum_nonneg (fun _ => norm_nonneg _)

/-! #### Norm Bounds -/

/- Aristotle failed to find a proof. -/
/-- The convolution exists for ℓ¹ functions. -/
theorem IsL1.convolutionExists (hf : IsL1 f) (hg : IsL1 g) : ConvolutionExists f g := by
  sorry

/- The convolution of ℓ¹ functions is in ℓ¹. -/
noncomputable section AristotleLemmas

/-
`sigmaMulFiberEquiv` is the equivalence between the disjoint union of fibers `Σ x, mulFiber x` and the product space `M × M`.
`tsum_mulFiber_eq_of_summable` states that summing a summable function `h` over `M × M` is equivalent to summing it over the fibers `mulFiber x` and then summing over `x`.
-/
def sigmaMulFiberEquiv : (Σ x : M, mulFiber x) ≃ M × M where
  toFun p := p.2.1
  invFun ab := ⟨ab.1 * ab.2, ab, rfl⟩
  left_inv := fun ⟨x, ab, h⟩ => by cases h; rfl
  right_inv := fun ab => rfl

theorem tsum_mulFiber_eq_of_summable {h : M × M → ℝ} (h_sum : Summable h) :
    (∑' x, ∑' ab : mulFiber x, h ab.1) = ∑' ab, h ab := by
  convert Summable.tsum_sigma' _ _;
  rotate_left;
  rotate_left;
  all_goals try infer_instance;
  exact fun _ => Unit;
  use fun p => h p.1;
  · exact fun _ => ⟨ _, hasSum_fintype _ ⟩;
  · convert h_sum.comp_injective ( show Function.Injective ( fun p : ( Σ x : M × M, Unit ) => p.1 ) from fun p q h => by aesop ) using 1;
  · rw [ Summable.tsum_sigma' ];
    · rw [ ← Equiv.tsum_eq ( Equiv.sigmaFiberEquiv ( fun x : M × M => x.1 * x.2 ) ) ];
      simp +decide [ Equiv.sigmaFiberEquiv ];
      erw [ Summable.tsum_sigma' ];
      · rfl;
      · exact fun b => h_sum.comp_injective Subtype.coe_injective;
      · exact h_sum.comp_injective fun x y hxy => by aesop;
    · exact fun _ => ⟨ _, hasSum_fintype _ ⟩;
    · convert h_sum.comp_injective ( show Function.Injective ( fun p : ( Σ x : M × M, Unit ) => p.fst ) from fun p q h => by aesop ) using 1;
  · erw [ tsum_fintype ] ; simp +decide

end AristotleLemmas

theorem IsL1.convolution (hf : IsL1 f) (hg : IsL1 g) : IsL1 (f ⋆ g) := by
  -- Let `h (ab : M × M) := ‖f ab.1‖ * ‖g ab.2‖`.
  set h : M × M → ℝ := fun ab => ‖f ab.1‖ * ‖g ab.2‖;
  have h_sum : Summable h := by
    rw [ summable_prod_of_nonneg ];
    · norm_num +zetaDelta at *;
      exact ⟨ fun x => Summable.mul_left _ hg, by simpa only [ tsum_mul_left ] using hf.mul_right _ ⟩;
    · exact fun _ => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ );
  -- By `tsum_mulFiber_eq_of_summable h`, we have `Summable (fun x => ∑' ab : mulFiber x, h ab.1)`.
  have h_sum_fiber : Summable (fun x => ∑' ab : mulFiber x, h ab.1) := by
    have := tsum_mulFiber_eq_of_summable h_sum;
    contrapose! this;
    rw [ tsum_eq_zero_of_not_summable this ];
    refine' ne_of_lt ( Summable.tsum_pos .. );
    exact h_sum;
    exact fun _ => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ );
    exact Classical.choose ( show ∃ ab : M × M, 0 < ‖f ab.1‖ * ‖g ab.2‖ from not_forall_not.mp fun h' => this <| by simpa [ show h = fun _ => 0 from funext fun _ => le_antisymm ( le_of_not_gt fun h'' => h' _ h'' ) ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ] using summable_zero );
    exact Classical.choose_spec ( show ∃ ab : M × M, 0 < ‖f ab.1‖ * ‖g ab.2‖ from not_forall_not.mp fun h' => this <| by simpa [ show h = fun _ => 0 from funext fun _ => le_antisymm ( le_of_not_gt fun h'' => h' _ h'' ) ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ] using summable_zero );
  refine' h_sum_fiber.of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => _ );
  refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
  · exact Summable.of_nonneg_of_le ( fun _ => norm_nonneg _ ) ( fun _ => by simpa using norm_mul_le _ _ ) ( h_sum.comp_injective Subtype.coe_injective );
  · exact Summable.tsum_le_tsum ( fun _ => by simpa using norm_mul_le _ _ ) ( by exact Summable.of_nonneg_of_le ( fun _ => norm_nonneg _ ) ( fun _ => by simpa using norm_mul_le _ _ ) ( h_sum.comp_injective Subtype.coe_injective ) ) ( by exact h_sum.comp_injective Subtype.coe_injective )

/- Submultiplicativity: `‖f ⋆ g‖₁ ≤ ‖f‖₁ · ‖g‖₁`. -/
noncomputable section AristotleLemmas

/-
The equivalence between the sigma type of fibers `Σ x, mulFiber x` and the product space `M × M`. This is just `Equiv.sigmaFiberEquiv` applied to `mulMap`.
-/
def DiscreteConvolution.mulFiberEquiv {M : Type*} [Monoid M] : (Σ x : M, DiscreteConvolution.mulFiber x) ≃ M × M :=
  Equiv.sigmaFiberEquiv DiscreteConvolution.mulMap

/-
The function `(a, b) ↦ ‖f a * g b‖` is summable over `M × M` if `f` and `g` are L1.
-/
theorem DiscreteConvolution.summable_norm_mul_prod {M R : Type*} [Monoid M] [NormedRing R] {f g : M → R} (hf : DiscreteConvolution.IsL1 f) (hg : DiscreteConvolution.IsL1 g) :
    Summable (fun ab : M × M => ‖f ab.1 * g ab.2‖) := by
      exact?

/-
The double sum of `‖f a * g b‖` over fibers equals the sum over `M × M`.
-/
theorem DiscreteConvolution.tsum_mulFiber_norm_eq {M R : Type*} [Monoid M] [NormedRing R] {f g : M → R} (hf : DiscreteConvolution.IsL1 f) (hg : DiscreteConvolution.IsL1 g) :
    (∑' x, ∑' ab : DiscreteConvolution.mulFiber x, ‖f ab.1.1 * g ab.1.2‖) = ∑' ab : M × M, ‖f ab.1 * g ab.2‖ := by
      have h_sum_eq : ∑' x : M, ∑' ab : mulFiber x, ‖f ab.1.1 * g ab.1.2‖ = ∑' ab : (Σ x : M, DiscreteConvolution.mulFiber x), ‖f ab.2.1.1 * g ab.2.1.2‖ := by
        rw [ Summable.tsum_sigma' ];
        · intro x;
          have h_summable_fiber : Summable (fun ab : M × M => ‖f ab.1 * g ab.2‖) := by
            exact?;
          exact h_summable_fiber.comp_injective Subtype.coe_injective;
        · convert DiscreteConvolution.summable_norm_mul_prod hf hg |> Summable.comp_injective <| DiscreteConvolution.mulFiberEquiv.injective using 1;
      rw [ h_sum_eq, ← Equiv.tsum_eq ( DiscreteConvolution.mulFiberEquiv ) ];
      rfl

end AristotleLemmas

theorem l1Norm_convolution_le (hf : IsL1 f) (hg : IsL1 g) :
    l1Norm (f ⋆ g) ≤ l1Norm f * l1Norm g := by
  refine' le_trans ( Summable.tsum_le_tsum _ _ _ ) _;
  use fun x => ∑' ab : DiscreteConvolution.mulFiber x, ‖f ab.1.1 * g ab.1.2‖;
  · intro x;
    convert norm_tsum_le_tsum_norm _;
    have h_summable : Summable (fun ab : M × M => ‖f ab.1 * g ab.2‖) := by
      exact?;
    exact h_summable.comp_injective Subtype.coe_injective;
  · convert DiscreteConvolution.IsL1.convolution hf hg;
  · -- Apply the theorem that states the double sum is equal to the sum over M × M.
    have h_double_sum : ∑' x, ∑' ab : DiscreteConvolution.mulFiber x, ‖f ab.1.1 * g ab.1.2‖ = ∑' ab : M × M, ‖f ab.1 * g ab.2‖ := by
      exact?;
    contrapose! h_double_sum;
    rw [ tsum_eq_zero_of_not_summable h_double_sum ];
    -- Since $f$ and $g$ are not both zero, there exists some $ab \in M \times M$ such that $f ab.1 * g ab.2 \neq 0$.
    obtain ⟨ab, hab⟩ : ∃ ab : M × M, f ab.1 * g ab.2 ≠ 0 := by
      by_cases h_zero : ∀ ab : M × M, f ab.1 * g ab.2 = 0;
      · exact False.elim ( h_double_sum <| ⟨ _, hasSum_single 1 fun x hx => by aesop ⟩ );
      · exact not_forall.mp h_zero;
    refine' ne_of_lt ( lt_of_lt_of_le _ ( Summable.le_tsum _ ab ( fun _ _ => norm_nonneg _ ) ) );
    · exact norm_pos_iff.mpr hab;
    · exact?;
  · rw [ DiscreteConvolution.tsum_mulFiber_norm_eq hf hg, Summable.tsum_prod ];
    · -- Apply the triangle inequality to the inner sum.
      have h_inner : ∀ b : M, ∑' c : M, ‖f b * g c‖ ≤ ‖f b‖ * ∑' c : M, ‖g c‖ := by
        intro b;
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · exact fun i => norm_mul_le _ _;
        · exact Summable.of_nonneg_of_le ( fun c => norm_nonneg _ ) ( fun c => norm_mul_le _ _ ) ( Summable.mul_left _ hg );
        · exact Summable.mul_left _ hg;
      convert Summable.tsum_le_tsum h_inner _ _;
      · rw [ tsum_mul_right, DiscreteConvolution.l1Norm, DiscreteConvolution.l1Norm ];
      · exact?;
      · exact Summable.of_nonneg_of_le ( fun b => tsum_nonneg fun c => norm_nonneg _ ) h_inner ( hf.mul_right _ );
      · exact Summable.mul_right _ hf;
    · exact?

end NormedRing

/-! ### Algebraic Properties -/

section Algebraic

variable [Monoid M] [Semiring R] [TopologicalSpace R] [T2Space R]

/- Aristotle failed to find a proof. -/
/-- Convolution is associative (when all sums converge). -/
theorem convolution_assoc (f g h : M → R)
    (hfg : ConvolutionExists f g) (hgh : ConvolutionExists g h)
    (hfg_h : ConvolutionExists (f ⋆ g) h) (hf_gh : ConvolutionExists f (g ⋆ h)) :
    (f ⋆ g) ⋆ h = f ⋆ (g ⋆ h) := by
  sorry

variable [DecidableEq M]

/-- Left identity: `δ₁ ⋆ f = f`. -/
theorem delta_convolution (f : M → R) (hf : ConvolutionExists delta f) :
    delta ⋆ f = f := by
  -- By definition of convolution, we have
  funext x
  simp [DiscreteConvolution.convolution, DiscreteConvolution.delta];
  erw [ tsum_eq_single ⟨ ( 1, x ), by simp +decide ⟩ ] <;> aesop

/-- Right identity: `f ⋆ δ₁ = f`. -/
theorem convolution_delta (f : M → R) (hf : ConvolutionExists f delta) :
    f ⋆ delta = f := by
  funext x; exact (by
  simp +decide [ convolution, delta ];
  rw [ tsum_eq_single ⟨ ⟨ x, 1 ⟩, by simp +decide [ DiscreteConvolution.mulFiber ] ⟩ ] <;> simp +decide [ Pi.single_apply ];
  aesop)

end Algebraic

section Commutative

variable [CommMonoid M] [CommSemiring R] [TopologicalSpace R] [T2Space R]

/-- Commutativity for commutative monoids and commutative rings. -/
theorem convolution_comm (f g : M → R)
    (hfg : ConvolutionExists f g) (hgf : ConvolutionExists g f) :
    f ⋆ g = g ⋆ f := by
  funext x;
  simp +decide only [DiscreteConvolution.convolution];
  rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun ab : mulFiber x => ⟨ ( ab.1.2, ab.1.1 ), by simp +decide [ mul_comm ] at ab ⊢; aesop ⟩ ) ⟨ fun a => ?_, fun a => ?_ ⟩ ) ];
  all_goals simp +decide [ Prod.ext_iff ];
  · exact tsum_congr fun ab => by rw [ mul_comm ] ;
  · aesop;
  · rcases a with ⟨ ⟨ a, b ⟩, h ⟩ ; use b, a, by simpa [ mul_comm ] using h;

end Commutative

end DiscreteConvolution

end

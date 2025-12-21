import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Cauchy Product (Convolution) of Sequences

The Cauchy product of sequences `a, b : ℕ → R` is defined as:

  `(a ⋆ b)ₙ = Σₖ₊ₗ₌ₙ aₖ bₗ`

## Design Philosophy: Transport from PowerSeries

This file establishes ring axioms for the Cauchy product by **transporting** them
from `PowerSeries R`, rather than proving them directly via sum manipulations.

### The Key Insight

The Cauchy product `(a ⋆ b)ₙ` is exactly the coefficient of `Xⁿ` in the product
of formal power series `(Σ aₖ Xᵏ) · (Σ bₗ Xˡ)`. This is formalized as:

  `toPowerSeries (a ⋆ b) = toPowerSeries a * toPowerSeries b`

Since Mathlib already proves `CommSemiring (PowerSeries R)`, we get all ring
axioms (associativity, distributivity, identity, commutativity) for free.

### Scalar Compatibility

The instances `SMulCommClass` and `IsScalarTower` in `lpWeighted.lean` rely on:
- `smul_mul`: `(c • a) ⋆ b = c • (a ⋆ b)` (works in any Semiring)
- `mul_smul`: `a ⋆ (c • b) = c • (a ⋆ b)` (requires CommSemiring)

These enable `smul_mul_assoc` and `smul_comm` for the derivative formula in
`FrechetCauchyProduct.lean`.

## Main Results

### PowerSeries Connection
* `toPowerSeries_mul`: `toPowerSeries (a ⋆ b) = toPowerSeries a * toPowerSeries b`

### Ring Axioms (Transported)
* `assoc`: `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`
* `comm`: `a ⋆ b = b ⋆ a` (requires `CommSemiring`)
* `left_distrib`, `right_distrib`: Distributivity
* `one_mul`, `mul_one`: Identity element

### Scalar Compatibility
* `smul_mul`: `(c • a) ⋆ b = c • (a ⋆ b)`
* `mul_smul`: `a ⋆ (c • b) = c • (a ⋆ b)` (requires `CommSemiring`)

## Implementation Notes

### Why `CauchyProduct.apply` is not @[simp]

We deliberately do NOT mark `apply` as `@[simp]`. Keeping the `⋆` notation
abstract prevents issues where:

1. A hypothesis `h : (a ⋆ b) n = 0` uses folded notation
2. The goal `∑ kl ∈ antidiagonal n, a kl.1 * b kl.2 = 0` is unfolded
3. The `simp` tactic fails to match them

Use `rw [CauchyProduct.apply]` to explicitly unfold when needed.

## References

- Definition 7.4.2: Cauchy product definition
- Theorem 7.4.4: Ring axioms for Cauchy product
- Corollary 7.4.5: Commutativity for commutative coefficient rings
-/

open scoped BigOperators

noncomputable section

variable {R : Type*}

/-- Cauchy product (convolution) of sequences.

    `(a ⋆ b)ₙ = Σₖ₊ₗ₌ₙ aₖ bₗ`

    This is Definition 7.4.2, written using the antidiagonal formulation. -/
def CauchyProduct [Semiring R] (a b : ℕ → R) : ℕ → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

notation:70 a:70 " ⋆ " b:71 => CauchyProduct a b

namespace CauchyProduct

/-! ## Semiring Section

Results that only require `Semiring R`. This includes most ring axioms
except commutativity and right scalar multiplication. -/

section Semiring

variable [Semiring R]

/-! ### Basic API -/

/-- The Cauchy product evaluated at index n.

    **Note**: Deliberately NOT marked `@[simp]` to keep the `⋆` notation abstract.
    This prevents simp from unfolding in ways that break hypothesis matching.
    Use `rw [CauchyProduct.apply]` to explicitly unfold when needed. -/
lemma apply (a b : ℕ → R) (n : ℕ) :
    (a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-- Alternative form using range, matching Definition 7.4.2 exactly:
    `(a ⋆ b)ₙ = Σⱼ₌₀ⁿ aₙ₋ⱼ bⱼ` -/
lemma apply_range (a b : ℕ → R) (n : ℕ) :
    (a ⋆ b) n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  simp only [apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-! ### Connection to PowerSeries

This is the heart of the "transport from PowerSeries" approach.
We show that `CauchyProduct` is definitionally the same as `PowerSeries`
multiplication, then use this to import all ring axioms. -/

/-- Convert a sequence to a formal power series.

    This is the bridge between our sequence-based formulation and Mathlib's
    `PowerSeries` which has a verified `CommSemiring` instance. -/
def toPowerSeries (a : ℕ → R) : PowerSeries R := PowerSeries.mk a

@[simp]
lemma coeff_toPowerSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := PowerSeries.coeff_mk n a

/-- **Key theorem**: Cauchy product equals PowerSeries multiplication.

    This is the bridge that lets us transport all ring axioms from
    `CommSemiring (PowerSeries R)` without reproving them.

    Proof: Both are defined as `Σₖ₊ₗ₌ₙ aₖ bₗ`. -/
theorem toPowerSeries_mul (a b : ℕ → R) :
    toPowerSeries (a ⋆ b) = toPowerSeries a * toPowerSeries b := by
  ext n
  simp only [apply, toPowerSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk]

/-- Coefficient form of `toPowerSeries_mul`. -/
theorem eq_coeff_mul (a b : ℕ → R) (n : ℕ) :
    (a ⋆ b) n = PowerSeries.coeff n (toPowerSeries a * toPowerSeries b) := by
  rw [← coeff_toPowerSeries (a ⋆ b) n, toPowerSeries_mul]

/-! ### Ring Axioms (Transported from PowerSeries)

Each axiom follows the same pattern:
1. State the property for `PowerSeries` (which Mathlib proves)
2. Convert both sides using `toPowerSeries_mul`
3. Extract coefficients to get the sequence equality

This is more maintainable than direct sum manipulation proofs. -/

/-- **Associativity**: `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`

    Transported from `mul_assoc` on `PowerSeries R`. -/
theorem assoc (a b c : ℕ → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  apply funext; intro n
  have h := congrArg (PowerSeries.coeff n)
    (mul_assoc (toPowerSeries a) (toPowerSeries b) (toPowerSeries c))
  simp only [← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

/-- **Left distributivity**: `a ⋆ (b + c) = a ⋆ b + a ⋆ c`

    Direct proof via sum distribution (no PowerSeries needed). -/
theorem left_distrib (a b c : ℕ → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n
  simp only [Pi.add_apply, apply, mul_add, Finset.sum_add_distrib]

/-- **Right distributivity**: `(a + b) ⋆ c = a ⋆ c + b ⋆ c`

    Direct proof via sum distribution (no PowerSeries needed). -/
theorem right_distrib (a b c : ℕ → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n
  simp only [apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Zero absorbs on the left: `0 ⋆ a = 0` -/
theorem zero_mul (a : ℕ → R) : (0 : ℕ → R) ⋆ a = 0 := by
  ext n; simp only [apply, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

/-- Zero absorbs on the right: `a ⋆ 0 = 0` -/
theorem mul_zero (a : ℕ → R) : a ⋆ (0 : ℕ → R) = 0 := by
  ext n; simp only [apply, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-! ### Identity Element

The multiplicative identity is the Kronecker delta: `e₀ = 1, eₙ = 0` for `n ≥ 1`.

This corresponds to the power series `1 = 1 + 0·X + 0·X² + ...`.
See Theorem 7.4.6: "the sequence e defined by eₙ := δₙ,₀ is the identity element" -/

/-- The multiplicative identity sequence: `e₀ = 1, eₙ = 0` for `n ≥ 1`. -/
def one : ℕ → R := fun n => if n = 0 then 1 else 0

@[simp] lemma one_zero : (one : ℕ → R) 0 = 1 := rfl
@[simp] lemma one_succ (n : ℕ) : (one : ℕ → R) (n + 1) = 0 := rfl

theorem toPowerSeries_one : toPowerSeries (one : ℕ → R) = 1 := by
  ext n
  simp only [coeff_toPowerSeries, one, PowerSeries.coeff_one]

/-- **Left identity**: `one ⋆ a = a`

    Transported from `one_mul` on `PowerSeries R`. -/
theorem one_mul (a : ℕ → R) : one ⋆ a = a := by
  apply funext; intro n
  have h := congrArg (PowerSeries.coeff n) (_root_.one_mul (toPowerSeries a))
  rw [coeff_toPowerSeries, ← toPowerSeries_one, ← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

/-- **Right identity**: `a ⋆ one = a`

    Transported from `mul_one` on `PowerSeries R`. -/
theorem mul_one (a : ℕ → R) : a ⋆ one = a := by
  apply funext; intro n
  have h := congrArg (PowerSeries.coeff n) (_root_.mul_one (toPowerSeries a))
  rw [coeff_toPowerSeries, ← toPowerSeries_one, ← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

/-! ### Scalar Multiplication (Semiring Case)

Scalar multiplication by ring elements pulls out on the left.
This is used for `IsScalarTower` in lpWeighted.lean.

For pulling out on the right, see `mul_smul` which requires `CommSemiring`. -/

/-- Scalars pull out on the left: `(c • a) ⋆ b = c • (a ⋆ b)`

    This enables `IsScalarTower ℝ (l1Weighted ν) (l1Weighted ν)`. -/
theorem smul_mul (c : R) (a b : ℕ → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n
  simp only [apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-! ### Support Lemmas

Lemmas about sequences with finite support, useful for polynomial computations. -/

/-- If both sequences vanish beyond M, their Cauchy product vanishes beyond 2M. -/
lemma zero_of_support {a b : ℕ → R} {M : ℕ}
    (ha : ∀ n, M < n → a n = 0) (hb : ∀ n, M < n → b n = 0)
    (n : ℕ) (hn : 2 * M < n) :
    (a ⋆ b) n = 0 := by
  rw [apply]
  apply Finset.sum_eq_zero
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  by_cases hk : M < k
  · simp [ha k hk]
  · push_neg at hk
    have hl : M < l := by omega
    simp [hb l hl]

/-- Cauchy product split when first sequence has support in `[0, N]` and `n > N`:
    `(a ⋆ h)ₙ = a₀ hₙ + Σₖ₌₁ᴺ aₖ hₙ₋ₖ`

    Useful for fixed-point iterations where `a` is a finite polynomial. -/
lemma apply_of_support_le_split {a h : ℕ → R} {N n : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hn : N < n) :
    (a ⋆ h) n = a 0 * h n + ∑ k ∈ Finset.Icc 1 N, a k * h (n - k) := by
  rw [apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * h l)]
  have h_restrict : ∑ k ∈ Finset.range (n + 1), a k * h (n - k) =
      ∑ k ∈ Finset.range (N + 1), a k * h (n - k) := by
    symm
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k hk hk'
      simp only [Finset.mem_range] at hk hk'
      push_neg at hk'
      rw [ha k hk', MulZeroClass.zero_mul]
  rw [h_restrict]
  have h_range_eq : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [h_range_eq, Finset.sum_insert]
  · simp only [Nat.sub_zero]
  · simp only [Finset.mem_Icc]; omega

end Semiring

/-! ## CommSemiring Section

Results requiring commutativity of the coefficient ring. This includes
commutativity of the Cauchy product and right scalar multiplication. -/

section CommSemiring

variable [CommSemiring R]

/-- **Commutativity**: `a ⋆ b = b ⋆ a`

    Transported from `mul_comm` on `PowerSeries R`.
    This is what makes ℓ¹_ν a *commutative* Banach algebra (Corollary 7.4.5). -/
theorem comm (a b : ℕ → R) : a ⋆ b = b ⋆ a := by
  apply funext; intro n
  have h := congrArg (PowerSeries.coeff n)
    (mul_comm (toPowerSeries a) (toPowerSeries b))
  simp only [← toPowerSeries_mul, coeff_toPowerSeries] at h
  exact h

/-- Scalars pull out on the right: `a ⋆ (c • b) = c • (a ⋆ b)`

    Requires commutativity since we need `aₖ * (c * bₗ) = c * (aₖ * bₗ)`.
    This enables `SMulCommClass ℝ (l1Weighted ν) (l1Weighted ν)`. -/
theorem mul_smul (c : R) (a b : ℕ → R) : a ⋆ (c • b) = c • (a ⋆ b) := by
  ext n
  simp only [apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  ring

end CommSemiring

end CauchyProduct

end

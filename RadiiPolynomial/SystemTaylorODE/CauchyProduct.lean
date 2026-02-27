import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.SystemTaylorODE.DiscreteConvolution

open scoped BigOperators

noncomputable section

namespace SystemTaylorODE

variable {R : Type*}

/-- Cauchy product (convolution) of sequences:
`(a ⋆ b)_n = ∑_{k+l=n} a_k b_l`.

Ref: Def. 7.4.2, Eq. (7.15). -/
def CauchyProduct [Semiring R] (a b : ℕ → R) : ℕ → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

namespace CauchyProduct

section Semiring

variable [Semiring R]

lemma apply (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

lemma apply_range (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  simp only [apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

section TopologicalBridge

variable [TopologicalSpace R]

/-- On `ℕ`, `CauchyProduct` agrees with additive ring convolution from
`DiscreteConvolution` once `tsum` is reduced to the antidiagonal finite sum. -/
theorem eq_addRingConvolution (a b : ℕ → R) :
    CauchyProduct a b = DiscreteConvolution.addRingConvolution (M := ℕ) a b := by
  funext n
  simpa [CauchyProduct, DiscreteConvolution.addRingConvolution] using
    (DiscreteConvolution.addConvolution_eq_sum_antidiagonal
      (M := ℕ) (S := ℕ) (E := R) (E' := R) (F := R)
      (L := LinearMap.mul ℕ R) a b n).symm

end TopologicalBridge

/-- Associativity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.11). -/
theorem assoc (a b c : ℕ → R) :
    CauchyProduct (CauchyProduct a b) c = CauchyProduct a (CauchyProduct b c) := by
  ext n
  simp only [apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals intro x hx
  all_goals simp_all only [Finset.mem_sigma, Finset.mem_antidiagonal, Prod.mk.eta, Sigma.eta]
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact mul_assoc _ _ _

/-- Left distributivity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.12). -/
theorem left_distrib (a b c : ℕ → R) :
    CauchyProduct a (b + c) = CauchyProduct a b + CauchyProduct a c := by
  ext n
  simp only [Pi.add_apply, apply, mul_add, Finset.sum_add_distrib]

/-- Right distributivity of Cauchy product.

Ref: Def. 7.4.1, Eq. (7.12). -/
theorem right_distrib (a b c : ℕ → R) :
    CauchyProduct (a + b) c = CauchyProduct a c + CauchyProduct b c := by
  ext n
  simp only [Pi.add_apply, apply, add_mul, Finset.sum_add_distrib]

theorem zero_mul (a : ℕ → R) : CauchyProduct 0 a = 0 := by
  ext n
  simp only [apply, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

theorem mul_zero (a : ℕ → R) : CauchyProduct a 0 = 0 := by
  ext n
  simp only [apply, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-- Multiplicative identity sequence (`1,0,0,...`). -/
def one : ℕ → R := fun n => if n = 0 then 1 else 0

@[simp] lemma one_zero : (one : ℕ → R) 0 = 1 := rfl
@[simp] lemma one_succ (n : ℕ) : (one : ℕ → R) (n + 1) = 0 := rfl

/-- Left identity for Cauchy product.

Ref: Def. 7.4.1 (unit element). -/
theorem one_mul (a : ℕ → R) : CauchyProduct one a = a := by
  ext n
  simp only [apply, one]
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro kl hkl hne
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    have hk : kl.1 ≠ 0 := by
      intro hk0
      apply hne
      apply Prod.ext
      · exact hk0
      · simpa [hk0] using hsum
    simp [hk]
  · simp [Finset.mem_antidiagonal]

/-- Right identity for Cauchy product.

Ref: Def. 7.4.1 (unit element). -/
theorem mul_one (a : ℕ → R) : CauchyProduct a one = a := by
  ext n
  simp only [apply, one]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro kl hkl hne
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    have hk : kl.2 ≠ 0 := by
      intro hk0
      apply hne
      apply Prod.ext
      · simpa [hk0] using hsum
      · exact hk0
    simp [hk]
  · simp [Finset.mem_antidiagonal]

/-- Scalar compatibility on the left.

Ref: Def. 7.4.1, Eq. (7.13). -/
theorem smul_mul (c : R) (a b : ℕ → R) :
    CauchyProduct (c • a) b = c • CauchyProduct a b := by
  ext n
  simp only [apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma zero_of_support {a b : ℕ → R} {M : ℕ}
    (ha : ∀ n, M < n → a n = 0) (hb : ∀ n, M < n → b n = 0)
    (n : ℕ) (hn : 2 * M < n) :
    CauchyProduct a b n = 0 := by
  rw [apply]
  apply Finset.sum_eq_zero
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  by_cases hk : M < k
  · simp [ha k hk]
  · push_neg at hk
    have hl : M < l := by omega
    simp [hb l hl]

lemma apply_of_support_le_split {a h : ℕ → R} {N n : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hn : N < n) :
    CauchyProduct a h n = a 0 * h n + ∑ k ∈ Finset.Icc 1 N, a k * h (n - k) := by
  rw [apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * h l)]
  have h_restrict : ∑ k ∈ Finset.range (n + 1), a k * h (n - k) =
      ∑ k ∈ Finset.range (N + 1), a k * h (n - k) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hk hk'
      simp only [Finset.mem_range] at hk hk'
      push_neg at hk'
      rw [ha k hk', MulZeroClass.zero_mul]
  rw [h_restrict]
  have h_range_eq : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h_range_eq, Finset.sum_insert]
  · simp only [Nat.sub_zero]
  · simp only [Finset.mem_Icc]
    omega

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Commutativity of Cauchy product.

Ref: Thm. 7.4.4 and Cor. 7.4.5. -/
theorem comm (a b : ℕ → R) : CauchyProduct a b = CauchyProduct b a := by
  ext n
  rw [apply, apply]
  have hleft :
      (∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2) =
        ∑ p ∈ Finset.antidiagonal n, b p.2 * a p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm]
  have hswap :
      (∑ p ∈ Finset.antidiagonal n, b p.2 * a p.1) =
        ∑ p ∈ Finset.antidiagonal n, b p.1 * a p.2 := by
    simpa using
      (Finset.Nat.sum_antidiagonal_swap (n := n) (f := fun p : ℕ × ℕ => b p.1 * a p.2))
  exact hleft.trans hswap

/-- Scalar compatibility on the right.

Ref: Def. 7.4.1, Eq. (7.13). -/
theorem mul_smul (c : R) (a b : ℕ → R) :
    CauchyProduct a (c • b) = c • CauchyProduct a b := by
  ext n
  simp only [apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  ring

end CommSemiring

section PowerSeriesBridge

variable [Semiring R]

/-- Bridge object: the sequence `a : ℕ → R` as a formal power series. -/
def toPowerSeries (a : ℕ → R) : PowerSeries R := PowerSeries.mk a

@[simp] lemma coeff_toPowerSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := PowerSeries.coeff_mk n a

/-- On index `ℕ`, Cauchy product matches power-series multiplication coefficients. -/
theorem toPowerSeries_mul (a b : ℕ → R) :
    toPowerSeries (CauchyProduct a b) = toPowerSeries a * toPowerSeries b := by
  ext n
  simp only [CauchyProduct.apply, toPowerSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk]

/-- Coefficient form of the bridge:
`(a ⋆ b)_n = coeff n ((toPowerSeries a) * (toPowerSeries b))`. -/
theorem eq_coeff_mul (a b : ℕ → R) (n : ℕ) :
    CauchyProduct a b n = PowerSeries.coeff n (toPowerSeries a * toPowerSeries b) := by
  rw [← coeff_toPowerSeries (CauchyProduct a b) n, toPowerSeries_mul]

end PowerSeriesBridge

end CauchyProduct

end SystemTaylorODE

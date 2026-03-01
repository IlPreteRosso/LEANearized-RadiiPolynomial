import RadiiPolynomial.SystemTaylorODE.lpWeighted
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# `l1Weighted` Banach-Algebra Layer

This file adds the convolution-based algebra/ring structure on
`SystemTaylorODE.l1Weighted ν`.

It is intentionally separated from `lpWeighted.lean`, following the same split
used by Mathlib's `DiscreteConvolution` / `LpOneBanachAlgebra` setup.
-/

open scoped BigOperators

noncomputable section

namespace SystemTaylorODE

namespace l1Weighted

variable {ν : PosReal}

section CauchyProductBanachAlgebra

local notation:67 a:68 " ⋆ " b:67 => CauchyProduct a b

/-- Weight factorization on antidiagonal fibers: if `k + l = n`, then `ν^n = ν^k * ν^l`. -/
lemma antidiagonal_weight (n : ℕ) (k l : ℕ) (h : k + l = n) :
    (ν : ℝ) ^ n = (ν : ℝ) ^ k * (ν : ℝ) ^ l := by
  subst h
  rw [pow_add]

/-- Cauchy product preserves weighted `ℓ¹` membership.

Ref: Thm. 7.4.3 and Thm. 7.4.4 (closure in weighted `ℓ¹`). -/
lemma cauchy_mem {a b : ℕ → ℝ}
    (ha : lpWeighted.Mem ν 1 a) (hb : lpWeighted.Mem ν 1 b) :
    lpWeighted.Mem ν 1 (a ⋆ b) := by
  rw [l1Weighted.mem_iff] at ha hb ⊢
  let f := fun k => |a k| * (ν : ℝ) ^ k
  let g := fun l => |b l| * (ν : ℝ) ^ l
  have hf_nn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) k)
  have hg_nn : ∀ l, 0 ≤ g l := fun l => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) l)
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    Summable.mul_of_nonneg ha hb hf_nn hg_nn
  have hsum := summable_sum_mul_antidiagonal_of_summable_mul hprod
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) n)
  · intro n
    refine (le_trans
      (b := (∑ kl ∈ Finset.antidiagonal n, |a kl.1| * |b kl.2|) * (ν : ℝ) ^ n)
      (c := ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) ?_ ?_)
    · refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (PosReal.coe_nonneg ν) n)
      rw [CauchyProduct.apply]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [abs_mul])
    · exact le_of_eq (by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro kl hkl
        rw [antidiagonal_weight (ν := ν) n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]
        simp [f, g]
        ring)
  · exact hsum

/-- Multiplication on `l1Weighted` via Cauchy product. -/
@[simp] def mul (a b : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) (cauchy_mem a.2 b.2)

/-- Submultiplicativity of the weighted `ℓ¹` norm.

Ref: Def. 7.4.1, Eq. (7.14); Thm. 7.4.4, Eq. (7.17). -/
lemma norm_mul_le (a b : l1Weighted ν) : ‖mul a b‖ ≤ ‖a‖ * ‖b‖ := by
  simp only [mul]
  rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  let f := fun k => |lpWeighted.toSeq a k| * (ν : ℝ) ^ k
  let g := fun l => |lpWeighted.toSeq b l| * (ν : ℝ) ^ l
  have hf_nn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) k)
  have hg_nn : ∀ l, 0 ≤ g l := fun l => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) l)
  have hf : Summable f := (l1Weighted.mem_iff _).mp a.2
  have hg : Summable g := (l1Weighted.mem_iff _).mp b.2
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    Summable.mul_of_nonneg hf hg hf_nn hg_nn
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod]
  refine Summable.tsum_le_tsum ?_ ((l1Weighted.mem_iff _).mp (cauchy_mem a.2 b.2))
    (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  intro n
  simp only [lpWeighted.mk_apply]
  refine (le_trans
    (b := (∑ kl ∈ Finset.antidiagonal n,
      |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2|) * (ν : ℝ) ^ n)
    (c := ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) ?_ ?_)
  · refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (PosReal.coe_nonneg ν) n)
    rw [CauchyProduct.apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [abs_mul])
  · exact le_of_eq (by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro kl hkl
      rw [antidiagonal_weight (ν := ν) n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]
      simp [f, g]
      ring)

lemma mul_comm (a b : l1Weighted ν) : mul a b = mul b a := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply]
  rw [CauchyProduct.comm]

lemma mul_assoc (a b c : l1Weighted ν) : mul (mul a b) c = mul a (mul b c) := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply]
  exact congrFun (CauchyProduct.assoc _ _ _) n

lemma left_distrib (a b c : l1Weighted ν) : mul a (b + c) = mul a b + mul a c := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.add_toSeq]
  exact congrFun (CauchyProduct.left_distrib _ _ _) n

lemma right_distrib (a b c : l1Weighted ν) : mul (a + b) c = mul a c + mul b c := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.add_toSeq]
  exact congrFun (CauchyProduct.right_distrib _ _ _) n

lemma zero_mul (a : l1Weighted ν) : mul 0 a = 0 := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.zero_toSeq]
  exact congrFun (CauchyProduct.zero_mul _) n

lemma mul_zero (a : l1Weighted ν) : mul a 0 = 0 := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.zero_toSeq]
  exact congrFun (CauchyProduct.mul_zero _) n

lemma one_mem (ν : PosReal) : lpWeighted.Mem ν 1 CauchyProduct.one := by
  rw [l1Weighted.mem_iff]
  refine summable_of_ne_finset_zero (s := {0}) ?_
  intro n hn
  have hn0 : n ≠ 0 := by
    simpa [Finset.mem_singleton] using hn
  simp [CauchyProduct.one, hn0]

/-- Multiplicative identity in weighted `ℓ¹`. -/
def one (ν : PosReal) : l1Weighted ν := lpWeighted.mk CauchyProduct.one (one_mem ν)

@[simp] lemma one_toSeq_zero : lpWeighted.toSeq (one ν) 0 = 1 := rfl
@[simp] lemma one_toSeq_succ (n : ℕ) : lpWeighted.toSeq (one ν) (n + 1) = 0 := rfl
@[simp] lemma one_toSeq : lpWeighted.toSeq (one ν) = CauchyProduct.one := rfl

lemma mul_one (a : l1Weighted ν) : mul a (one ν) = a := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, one_toSeq]
  rw [CauchyProduct.mul_one]

lemma one_mul (a : l1Weighted ν) : mul (one ν) a = a := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply, one_toSeq]
  rw [CauchyProduct.one_mul]

lemma norm_one (ν : PosReal) : ‖one ν‖ = 1 := by
  rw [l1Weighted.norm_eq_tsum]
  rw [show (fun n => |lpWeighted.toSeq (one ν) n| * (ν : ℝ) ^ n) = fun n => if n = 0 then 1 else 0 from by
    funext n
    cases n with
    | zero => simp [one, CauchyProduct.one, lpWeighted.mk]
    | succ n => simp [one, CauchyProduct.one, lpWeighted.mk]]
  rw [tsum_ite_eq]

/-- Ring structure from Cauchy product.

Ref: Def. 7.4.1, Eqs. (7.11)–(7.13). -/
instance instRing : Ring (l1Weighted ν) where
  mul := mul
  mul_assoc := mul_assoc
  one := one ν
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero

/-- Commutative ring structure on `l1Weighted ν`.

Ref: Thm. 7.4.4 and Cor. 7.4.5. -/
instance instCommRing : CommRing (l1Weighted ν) where
  mul_comm := mul_comm

/-- Normed ring structure with submultiplicative norm.

Ref: Def. 7.4.1, Eq. (7.14); Thm. 7.4.4, Eq. (7.17). -/
instance instNormedRing : NormedRing (l1Weighted ν) where
  dist_eq := fun _ _ => rfl
  norm_mul_le := norm_mul_le

/-- Normalized unit element.

Ref: Def. 7.4.1 (unit element). -/
instance instNormedCommRing : NormedCommRing (l1Weighted ν) where
  dist_eq := fun _ _ => rfl
  norm_mul_le := norm_mul_le
  mul_comm := mul_comm

instance instNormOneClass : NormOneClass (l1Weighted ν) where
  norm_one := norm_one ν

instance instSMulCommClass : SMulCommClass ℝ (l1Weighted ν) (l1Weighted ν) where
  smul_comm c a b := by
    change c • (a * b) = a * (c • b)
    apply lpWeighted.ext
    intro n
    simp only [lpWeighted.toSeq_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    exact congrFun (CauchyProduct.mul_smul c a.val b.val).symm n

instance instIsScalarTower : IsScalarTower ℝ (l1Weighted ν) (l1Weighted ν) where
  smul_assoc c a b := by
    change (c • a) * b = c • (a * b)
    apply lpWeighted.ext
    intro n
    simp only [lpWeighted.toSeq_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    exact congrFun (CauchyProduct.smul_mul c a.val b.val) n

instance instAlgebra : Algebra ℝ (l1Weighted ν) := Algebra.ofModule
  (fun r a b => smul_mul_assoc r a b)
  (fun r a b => mul_smul_comm r a b)

@[simp] lemma algebraMap_apply (r : ℝ) : algebraMap ℝ (l1Weighted ν) r = r • 1 := rfl

lemma norm_algebraMap (r : ℝ) : ‖algebraMap ℝ (l1Weighted ν) r‖ = ‖r‖ := by
  simp only [algebraMap_apply, norm_smul, Real.norm_eq_abs, NormOneClass.norm_one, _root_.mul_one]

instance instNormedAlgebra : NormedAlgebra ℝ (l1Weighted ν) where
  norm_smul_le := fun r a => by rw [norm_smul]

end CauchyProductBanachAlgebra

/-! ### Left multiplication CLM (alias to Mathlib's `ContinuousLinearMap.mul`)

`leftMul a` is left-multiplication by `a` as a CLM.
Delegates to `ContinuousLinearMap.mul ℝ (l1Weighted ν)`, which provides:
- `mul_apply' : leftMul a h = a * h`  (simp)
- `opNorm_mul_apply_le : ‖leftMul a‖ ≤ ‖a‖`  (simp)
- `.map_add`, `.map_smul`, `.map_sub` for linearity
-/

noncomputable abbrev leftMul (a : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  ContinuousLinearMap.mul ℝ (l1Weighted ν) a

@[simp] lemma leftMul_apply (a h : l1Weighted ν) : leftMul a h = a * h := rfl

lemma norm_leftMul_le (a : l1Weighted ν) : ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le _ _ a

lemma leftMul_add (a b : l1Weighted ν) :
    leftMul (a + b) = leftMul a + leftMul b :=
  map_add (ContinuousLinearMap.mul ℝ (l1Weighted ν)) a b

lemma leftMul_sub (a b : l1Weighted ν) :
    leftMul (a - b) = leftMul a - leftMul b :=
  map_sub (ContinuousLinearMap.mul ℝ (l1Weighted ν)) a b

lemma leftMul_smul (c : ℝ) (a : l1Weighted ν) :
    leftMul (c • a) = c • leftMul a :=
  (ContinuousLinearMap.mul ℝ (l1Weighted ν)).map_smul c a

/-- Bridge: Mathlib canonical `a • .id` ↔ `leftMul a`.
Used by `derive_fderiv` to normalize `(n • a^k) • .id` to `leftMul` form. -/
lemma smul_id_eq_leftMul (a : l1Weighted ν) :
    a • ContinuousLinearMap.id ℝ (l1Weighted ν) = leftMul a := by
  ext h; simp [smul_eq_mul]

/-- Bridge: convert ℕ-smul inside `leftMul` to ℝ-smul.
Handles arbitrary degree: `leftMul (n • a) = (↑n : ℝ) • leftMul a`. -/
lemma leftMul_nsmul (n : ℕ) (a : l1Weighted ν) :
    leftMul (n • a) = (↑n : ℝ) • leftMul a := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n a, leftMul_smul]

end l1Weighted

end SystemTaylorODE

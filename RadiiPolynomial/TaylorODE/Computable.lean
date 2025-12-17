import RadiiPolynomial.TaylorODE.ScaledReal
import RadiiPolynomial.TaylorODE.CauchyProduct
import RadiiPolynomial.TaylorODE.lpWeighted
import RadiiPolynomial.TaylorODE.OperatorNorm
import RadiiPolynomial.TaylorODE.Example_7_7
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Matrix.Basic

/-!
# Computational Reflection for Weighted ℓ¹ Spaces

This file provides computable versions of key operations and reflection lemmas
that allow `native_decide` to verify bounds when inputs are rational.

## Strategy

For each abstract ℝ operation, we provide:
1. A computable ℚ version
2. A reflection lemma: `abstract_ℝ (↑q) = ↑(computable_ℚ q)`

This bridges the gap between abstract Mathlib definitions and numerical verification.
-/

open scoped Matrix


/-! ## IsRat: Typeclass for ℝ values that are really ℚ

Inspired by ComputableReal's IsComputable typeclass.
Source: https://github.com/Timeroot/ComputableReal.git

Tracks that an ℝ value equals a specific ℚ, enabling decidable comparisons.
-/

/-- Typeclass asserting that `x : ℝ` equals `IsRat.q x` for some rational -/
class IsRat (x : ℝ) where
  q : ℚ
  eq : x = (q : ℝ)

namespace IsRat

instance instRat (r : ℚ) : IsRat (r : ℝ) := ⟨r, rfl⟩
instance instNat (n : ℕ) : IsRat (n : ℝ) := ⟨n, by simp⟩
instance instInt (z : ℤ) : IsRat (z : ℝ) := ⟨z, by simp⟩
instance instOfNat0 : IsRat (0 : ℝ) := ⟨0, by simp⟩
instance instOfNat1 : IsRat (1 : ℝ) := ⟨1, by simp⟩

instance instNeg [hx : IsRat x] : IsRat (-x) :=
  ⟨-hx.q, by simp [hx.eq]⟩

instance instInv [hx : IsRat x] : IsRat (x⁻¹) :=
  ⟨hx.q⁻¹, by simp [hx.eq]⟩

instance instAdd [hx : IsRat x] [hy : IsRat y] : IsRat (x + y) :=
  ⟨hx.q + hy.q, by simp [hx.eq, hy.eq]⟩

instance instSub [hx : IsRat x] [hy : IsRat y] : IsRat (x - y) :=
  ⟨hx.q - hy.q, by simp [hx.eq, hy.eq]⟩

instance instMul [hx : IsRat x] [hy : IsRat y] : IsRat (x * y) :=
  ⟨hx.q * hy.q, by simp [hx.eq, hy.eq]⟩

instance instDiv [hx : IsRat x] [hy : IsRat y] : IsRat (x / y) :=
  ⟨hx.q / hy.q, by simp [hx.eq, hy.eq]⟩

instance instPow [hx : IsRat x] (n : ℕ) : IsRat (x ^ n) :=
  ⟨hx.q ^ n, by simp [hx.eq]⟩

instance instAbs [hx : IsRat x] : IsRat |x| :=
  ⟨|hx.q|, by simp [hx.eq]⟩

/-- Decidable ≤ for IsRat values -/
instance instDecidableLE [hx : IsRat x] [hy : IsRat y] : Decidable (x ≤ y) :=
  decidable_of_iff (hx.q ≤ hy.q) (by simp [hx.eq, hy.eq])

/-- Decidable < for IsRat values -/
instance instDecidableLT [hx : IsRat x] [hy : IsRat y] : Decidable (x < y) :=
  decidable_of_iff (hx.q < hy.q) (by simp [hx.eq, hy.eq])

/-- Decidable = for IsRat values -/
instance instDecidableEq [hx : IsRat x] [hy : IsRat y] : Decidable (x = y) :=
  decidable_of_iff (hx.q = hy.q) (by simp [hx.eq, hy.eq])

end IsRat


/-! ## Positive Rationals -/

/-- Positive rationals -/
structure PosRat where
  val : ℚ
  pos : 0 < val
  deriving DecidableEq

namespace PosRat

instance : Coe PosRat ℚ := ⟨PosRat.val⟩

@[simp] lemma coe_pos (ν : PosRat) : (0 : ℚ) < ν.val := ν.pos

/-- Convert to PosReal -/
noncomputable def toPosReal (ν : PosRat) : PosReal := ⟨ν.val, by exact_mod_cast ν.pos⟩

@[simp] lemma toPosReal_val (ν : PosRat) : (ν.toPosReal : ℝ) = (ν.val : ℝ) := rfl

end PosRat


/-! ## Computable Absolute Value -/

/-- Computable absolute value on ℚ -/
def Rat.abs (q : ℚ) : ℚ := if q < 0 then -q else q

@[simp] lemma Rat.abs_nonneg (q : ℚ) : 0 ≤ Rat.abs q := by
  simp only [Rat.abs]
  split_ifs with h
  · linarith
  · linarith

lemma Rat.abs_eq_abs (q : ℚ) : (Rat.abs q : ℝ) = |q| := by
  simp only [Rat.abs]
  split_ifs with h
  · simp only [cast_neg, cast_abs]
    rw [abs_of_neg (by exact_mod_cast h)]
  · push_neg at h
    rw [abs_of_nonneg (by exact_mod_cast h)]


/-! ## Computable Scaled Norm -/

/-- Computable scaled norm: |x| * ν^n -/
def scaledNorm_rat (ν : ℚ) (n : ℕ) (x : ℚ) : ℚ := Rat.abs x * ν ^ n

/-- Reflection: scaledNorm on ℚ inputs equals ℚ computation -/
lemma scaledNorm_eq_rat (ν : PosRat) (n : ℕ) (x : ℚ) :
    |x| * (ν.toPosReal : ℝ) ^ n = (scaledNorm_rat ν.val n x : ℝ) := by
  simp only [scaledNorm_rat, PosRat.toPosReal_val, Rat.cast_mul, Rat.cast_pow]
  rw [Rat.abs_eq_abs]


/-! ## Computable Weighted ℓ¹ Norm (Finite) -/

/-- Computable finite weighted ℓ¹ norm: Σᵢ |xᵢ| * νⁱ -/
def finl1Norm_rat (ν : ℚ) (x : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, Rat.abs (x i) * ν ^ (i : ℕ)

/-- Reflection for finite weighted norm -/
lemma finl1Norm_eq_rat (ν : PosRat) (x : Fin n → ℚ) :
    ∑ i : Fin n, |x i| * (ν.toPosReal : ℝ) ^ (i : ℕ) = (finl1Norm_rat ν.val x : ℝ) := by
  simp only [finl1Norm_rat, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, PosRat.toPosReal_val]
  congr 1
  ext i
  rw [Rat.abs_eq_abs]


/-! ## Computable Matrix Column Norm -/

/-- Computable column norm: (1/ν^j) * Σᵢ |Aᵢⱼ| * νⁱ -/
def matrixColNorm_rat (ν : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) (j : Fin n) : ℚ :=
  (1 / ν ^ (j : ℕ)) * ∑ i : Fin m, Rat.abs (A i j) * ν ^ (i : ℕ)

/-- Computable matrix norm: max over columns -/
def finWeightedMatrixNorm_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => matrixColNorm_rat ν A j)


/-! ## Computable Cauchy Product (Finite) -/

/-- Computable Cauchy product at index n -/
def cauchyProduct_rat (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- Cauchy product for finite sequences (zero-padded) -/
def cauchyProductFin_rat (a b : Fin (n+1) → ℚ) (k : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal k,
    (if hij : ij.1 ≤ n then a ⟨ij.1, Nat.lt_succ_of_le hij⟩ else 0) *
    (if hij : ij.2 ≤ n then b ⟨ij.2, Nat.lt_succ_of_le hij⟩ else 0)


/-! ## Example: Reflection for Y₀ Finite Part

The finite part of Y₀ is: Σᵢ |Σⱼ Aᵢⱼ * Fⱼ| * νⁱ

This is computable when A, F are rational matrices/vectors.
-/

/-- Computable matrix-vector product -/
def matVecMul_rat (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) : Fin m → ℚ :=
  fun i => ∑ j : Fin n, A i j * v j

/-- Computable Y₀ finite part: Σᵢ |[A·v]ᵢ| * νⁱ -/
def Y₀_fin_rat (ν : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin m, Rat.abs (matVecMul_rat A v i) * ν ^ (i : ℕ)


/-! ## Decidability for ℚ comparisons -/

-- ℚ has decidable ordering via LinearOrder
instance : DecidableRel ((· < ·) : ℚ → ℚ → Prop) := inferInstance
instance : DecidableRel ((· ≤ ·) : ℚ → ℚ → Prop) := inferInstance


/-! ## Computable Max (Finset.sup') -/

/-- Computable max over a Finset -/
def finsetMax_rat (s : Finset α) (hs : s.Nonempty) (f : α → ℚ) : ℚ :=
  s.sup' hs f

/-- Reflection for Finset.sup' when f maps to ℚ -/
lemma finsetSup'_eq_rat (s : Finset α) (hs : s.Nonempty) (f : α → ℚ) :
    ((s.sup' hs f : ℚ) : ℝ) = s.sup' hs (fun a => (f a : ℝ)) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd rfl (Finset.Nonempty.ne_empty hs)
  | cons a s ha ih =>
    by_cases hs' : s.Nonempty
    · have : (Finset.cons a s ha).sup' hs f = f a ⊔ s.sup' hs' f := Finset.sup'_cons hs' f
      rw [this, Rat.cast_max, ih hs']
      rw [Finset.sup'_cons hs' (fun a => (f a : ℝ))]
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs'
      subst hs'
      simp [Finset.sup'_singleton]

/-- Expansion for finWeightedMatrixNorm_rat -/
lemma finWeightedMatrixNorm_rat_eq_sup' (ν : PosRat) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (finWeightedMatrixNorm_rat ν.val A : ℝ) =
    Finset.univ.sup' Finset.univ_nonempty (fun j => (matrixColNorm_rat ν.val A j : ℝ)) := by
  unfold finWeightedMatrixNorm_rat
  rw [finsetSup'_eq_rat]


/-! ## Finite Sequence as Zero-Padded Infinite Sequence -/

/-- Zero-pad a finite sequence -/
def finToSeq_rat (x : Fin (n+1) → ℚ) : ℕ → ℚ := fun k =>
  if h : k ≤ n then x ⟨k, Nat.lt_succ_of_le h⟩ else 0

@[simp] lemma finToSeq_rat_lt (x : Fin (n+1) → ℚ) (k : ℕ) (hk : k ≤ n) :
    finToSeq_rat x k = x ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [finToSeq_rat, hk]

@[simp] lemma finToSeq_rat_ge (x : Fin (n+1) → ℚ) (k : ℕ) (hk : n < k) :
    finToSeq_rat x k = 0 := by
  simp [finToSeq_rat, Nat.not_le.mpr hk]


/-! ## Computable Cauchy Product with Reflection -/

/-- Cauchy product at index k for zero-padded sequences -/
def cauchyProduct_fin_rat (a b : Fin (n+1) → ℚ) (k : ℕ) : ℚ :=
  cauchyProduct_rat (finToSeq_rat a) (finToSeq_rat b) k

/-- Component-wise Cauchy product definition -/
lemma cauchyProduct_fin_rat_eq (a b : Fin (n+1) → ℚ) (k : ℕ) :
    cauchyProduct_fin_rat a b k =
    ∑ ij ∈ Finset.antidiagonal k, finToSeq_rat a ij.1 * finToSeq_rat b ij.2 := rfl

/-- Reflection: CauchyProduct on ℚ sequences casts correctly -/
lemma cauchyProduct_cast (a b : ℕ → ℚ) (k : ℕ) :
    (cauchyProduct_rat a b k : ℝ) = ((fun i => (a i : ℝ)) ⋆ (fun i => (b i : ℝ))) k := by
  simp only [cauchyProduct_rat, CauchyProduct.apply, Rat.cast_sum, Rat.cast_mul]


/-! ## F(ā) = ā ⋆ ā - c computation -/

/-- Computable F₀ = ā₀² - λ₀ -/
def F_component_rat (a : Fin (n+1) → ℚ) (c : ℕ → ℚ) (k : ℕ) : ℚ :=
  cauchyProduct_fin_rat a a k - c k

/-- The paramSeq c = (λ₀, 1, 0, 0, ...) -/
def paramSeq_rat (lam0 : ℚ) : ℕ → ℚ
  | 0 => lam0
  | 1 => 1
  | _ => 0

@[simp] lemma paramSeq_rat_zero (lam0 : ℚ) : paramSeq_rat lam0 0 = lam0 := rfl
@[simp] lemma paramSeq_rat_one (lam0 : ℚ) : paramSeq_rat lam0 1 = 1 := rfl
@[simp] lemma paramSeq_rat_ge_two (lam0 : ℚ) (k : ℕ) (hk : 2 ≤ k) : paramSeq_rat lam0 k = 0 := by
  match k with
  | 0 | 1 => omega
  | k + 2 => rfl


/-! ## Full Y₀ Computation -/

/-- Y₀ finite part: Σᵢ₌₀ᴺ |[A·F(ā)]ᵢ| * νⁱ -/
def Y₀_finite_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (a : Fin (n+1) → ℚ) (lam0 : ℚ) : ℚ :=
  ∑ i : Fin (n+1), Rat.abs (∑ j : Fin (n+1), A i j * F_component_rat a (paramSeq_rat lam0) j) * ν ^ (i : ℕ)

/-- Y₀ tail part: (1/(2|ā₀|)) * Σₙ₌ₙ₊₁²ᴺ (Σ convolution terms) * νⁿ -/
def Y₀_tail_rat (ν : ℚ) (a : Fin (n+1) → ℚ) : ℚ :=
  (1 / (2 * Rat.abs (a 0))) *
  ∑ k ∈ Finset.Icc (n + 1) (2 * n),
    (∑ ij ∈ Finset.Icc (k - n) n,
      Rat.abs (finToSeq_rat a ij) * Rat.abs (finToSeq_rat a (k - ij))) * ν ^ k

/-- Full Y₀ bound -/
def Y₀_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (a : Fin (n+1) → ℚ) (lam0 : ℚ) : ℚ :=
  Y₀_finite_rat ν A a lam0 + Y₀_tail_rat ν a


/-! ## Z₁ Computation (simplest) -/

/-- Z₁ = (1/|ā₀|) * Σₙ₌₁ᴺ |āₙ| * νⁿ -/
def Z₁_rat (ν : ℚ) (a : Fin (n+1) → ℚ) : ℚ :=
  (1 / Rat.abs (a 0)) * ∑ k ∈ Finset.Icc 1 n, Rat.abs (finToSeq_rat a k) * ν ^ k


/-! ## Z₀ Computation -/

/-- DF(ā) finite block: 2 * lower triangular Toeplitz from ā.
    Takes raw ℚ vector. Used by Z₀_rat, Z₂_rat. -/
def DF_fin_rat (a : Fin (n+1) → ℚ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => if j ≤ i then 2 * a ⟨i - j, by omega⟩ else 0

/-- I - A·DF(ā) -/
def IADF_rat (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (a : Fin (n+1) → ℚ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  1 - A * DF_fin_rat a

/-- Z₀ = ‖I - A·DF(ā)‖_{1,ν} -/
def Z₀_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (a : Fin (n+1) → ℚ) : ℚ :=
  finWeightedMatrixNorm_rat ν (IADF_rat A a)


/-! ## Z₂ Computation -/

/-- Z₂ = 2 * max(‖A‖_{1,ν}, 1/(2|ā₀|)) -/
def Z₂_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (a : Fin (n+1) → ℚ) : ℚ :=
  2 * max (finWeightedMatrixNorm_rat ν A) (1 / (2 * Rat.abs (a 0)))


/-! ## Full Radii Polynomial -/

/-- p(r) = Z₂·r² - (1 - Z₀ - Z₁)·r + Y₀ -/
def radiiPoly_rat (Y₀ Z₀ Z₁ Z₂ r : ℚ) : ℚ :=
  Z₂ * r^2 - (1 - Z₀ - Z₁) * r + Y₀

/-- All-in-one radii polynomial computation -/
def computeRadiiPoly_rat (ν : ℚ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (a : Fin (n+1) → ℚ) (lam0 r : ℚ) : ℚ :=
  radiiPoly_rat (Y₀_rat ν A a lam0) (Z₀_rat ν A a) (Z₁_rat ν a) (Z₂_rat ν A a) r


/-! ## Reflection Lemmas: Abstract ℝ = Computable ℚ

These lemmas bridge abstract Mathlib definitions to computable ℚ versions,
enabling `native_decide` verification of bounds.
-/

section Reflection

variable {n : ℕ}

/-- Cast ℚ matrix to ℝ matrix -/
def Matrix.castRat (A : Matrix (Fin m) (Fin k) ℚ) : Matrix (Fin m) (Fin k) ℝ :=
  fun i j => (A i j : ℝ)

/-- Cast ℚ vector to ℝ vector -/
def Fin.castRat (v : Fin k → ℚ) : Fin k → ℝ := fun i => (v i : ℝ)

/-- Reflection for matrixColNorm -/
lemma matrixColNorm_eq_rat (ν : PosRat) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (j : Fin (n+1)) :
    l1Weighted.matrixColNorm ν.toPosReal (Matrix.castRat A) j =
    (matrixColNorm_rat ν.val A j : ℝ) := by
  simp only [l1Weighted.matrixColNorm, matrixColNorm_rat, Matrix.castRat]
  simp only [PosRat.toPosReal_val]
  rw [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_pow]
  congr 1
  rw [Rat.cast_sum]
  congr 1
  ext i
  rw [Rat.cast_mul, Rat.cast_pow, Rat.abs_eq_abs]; congr
  rw [Rat.cast_abs]

/-- Reflection for finWeightedMatrixNorm -/
lemma finWeightedMatrixNorm_eq_rat (ν : PosRat) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    l1Weighted.finWeightedMatrixNorm ν.toPosReal (Matrix.castRat A) =
    (finWeightedMatrixNorm_rat ν.val A : ℝ) := by
  simp only [l1Weighted.finWeightedMatrixNorm, finWeightedMatrixNorm_rat]
  rw [finsetSup'_eq_rat]
  congr 1
  ext j
  exact matrixColNorm_eq_rat ν A j

/-- Reflection for Z₁_bound: (1/|ā₀|) * Σₙ₌₁ᴺ |āₙ| * νⁿ -/
lemma Z₁_bound_eq_rat (ν : PosRat) (a : Fin (n+1) → ℚ) :
    (1 / |Fin.castRat a 0|) * ∑ k ∈ Finset.Icc 1 n, |finToSeq_rat a k| * (ν.toPosReal : ℝ) ^ k =
    (Z₁_rat ν.val a : ℝ) := by
  simp only [Z₁_rat, Fin.castRat, PosRat.toPosReal_val]
  rw [Rat.cast_mul, Rat.cast_div, Rat.cast_one]
  congr 1
  · rw [Rat.abs_eq_abs]; congr
    rw [Rat.cast_abs]
  · rw [Rat.cast_sum]
    congr 1
    ext k
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.abs_eq_abs]

/-- Helper: finToSeq_rat casts correctly -/
lemma finToSeq_rat_cast (a : Fin (n+1) → ℚ) (k : ℕ) :
    (finToSeq_rat a k : ℝ) =
    if h : k ≤ n then (a ⟨k, Nat.lt_succ_of_le h⟩ : ℝ) else 0 := by
  simp only [finToSeq_rat]
  split_ifs <;> simp

/-- Reflection for Cauchy product of finite ℚ sequences -/
lemma cauchyProduct_fin_eq_rat (a b : Fin (n+1) → ℚ) (k : ℕ) :
    ((fun i => (finToSeq_rat a i : ℝ)) ⋆ (fun i => (finToSeq_rat b i : ℝ))) k =
    (cauchyProduct_fin_rat a b k : ℝ) := by
  simp only [CauchyProduct.apply, cauchyProduct_fin_rat, cauchyProduct_rat]
  rw [Rat.cast_sum]
  congr 1
  ext ⟨i, j⟩
  simp only [Rat.cast_mul]

end Reflection


/-! ## ApproxSolution over ℚ

A ℚ version of ApproxSolution that enables computational reflection.
-/

section ApproxSolutionRat

variable {N : ℕ}

/-- Approximate solution with ℚ coefficients -/
structure ApproxSolution_rat (N : ℕ) where
  aBar_fin : Fin (N + 1) → ℚ
  aBar_zero_ne : aBar_fin 0 ≠ 0

namespace ApproxSolution_rat

/-- Convert to real ApproxSolution -/
noncomputable def toReal (a : ApproxSolution_rat N) : Example_7_7.ApproxSolution N where
  aBar_fin := fun i => (a.aBar_fin i : ℝ)
  aBar_zero_ne := by
    simp only [ne_eq, Rat.cast_eq_zero]
    exact a.aBar_zero_ne

/-- The ℚ sequence (zero-padded) -/
def toSeq_rat (a : ApproxSolution_rat N) : ℕ → ℚ := finToSeq_rat a.aBar_fin

@[simp]
lemma toReal_aBar_fin (a : ApproxSolution_rat N) (i : Fin (N + 1)) :
    a.toReal.aBar_fin i = (a.aBar_fin i : ℝ) := rfl

/-- toSeq of toReal = cast of toSeq_rat -/
lemma toReal_toSeq (a : ApproxSolution_rat N) (k : ℕ) :
    a.toReal.toSeq k = (a.toSeq_rat k : ℝ) := by
  simp only [Example_7_7.ApproxSolution.toSeq, toSeq_rat, finToSeq_rat]
  split_ifs with h
  · simp [toReal]
  · simp

/-- lpWeighted.toSeq of toL1 = cast of toSeq_rat -/
lemma toReal_toL1_toSeq (ν : PosReal) (a : ApproxSolution_rat N) (k : ℕ) :
    lpWeighted.toSeq (ν := ν) a.toReal.toL1 k = (a.toSeq_rat k : ℝ) := by
  simp only [Example_7_7.ApproxSolution.toL1, lpWeighted.mk_apply, toReal_toSeq]

end ApproxSolution_rat


/-! ## Matrix over ℚ -/

/-- ℚ matrix cast to ℝ -/
def Matrix.ofRat (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)

@[simp]
lemma Matrix.ofRat_apply (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    Matrix.ofRat A i j = (A i j : ℝ) := rfl


/-! ## Full Reflection Lemmas for Bounds -/

/-- DF(ā) finite block from ApproxSolution_rat.
    Same computation as DF_fin_rat, but takes ApproxSolution_rat instead of raw ℚ vector.
    Used for reflection lemmas connecting abstract Example_7_7.DF_fin to computable version. -/
def DF_fin_of_rat (a : ApproxSolution_rat N) : Matrix (Fin (N+1)) (Fin (N+1)) ℚ :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) then 2 * a.aBar_fin ⟨i - j, by omega⟩ else 0

/-- DF_fin reflection -/
lemma DF_fin_eq_rat (a : ApproxSolution_rat N) :
    Example_7_7.DF_fin a.toReal = Matrix.ofRat (DF_fin_of_rat a) := by
  ext i j
  simp only [Example_7_7.DF_fin, DF_fin_of_rat, Matrix.ofRat_apply, ApproxSolution_rat.toReal_aBar_fin, Matrix.of_apply]
  split_ifs with h
  · simp [Rat.cast_mul]
  · rw [Rat.cast_zero]

/-- Z₀_bound on ℚ inputs = Z₀_rat -/
lemma Z₀_bound_eq_rat' (ν : PosRat) (a : ApproxSolution_rat N)
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℚ) :
    @Example_7_7.Z₀_bound ν.toPosReal N a.toReal (Matrix.ofRat A) =
    (Z₀_rat ν.val A a.aBar_fin : ℝ) := by
  unfold Example_7_7.Z₀_bound Z₀_rat
  rw [DF_fin_eq_rat]
  -- I - A·DF is a ℚ matrix cast to ℝ
  have h_mat : (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) - Matrix.ofRat A * Matrix.ofRat (DF_fin_of_rat a) =
               Matrix.ofRat (1 - A * DF_fin_of_rat a) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.ofRat_apply]
    simp only [Rat.cast_sub, Rat.cast_sum, Rat.cast_mul]
    congr 1; split_ifs <;> simp
  rw [h_mat]
  exact finWeightedMatrixNorm_eq_rat ν (1 - A * DF_fin_of_rat a)

lemma Z₂_bound_eq_rat' (ν : PosRat) (a : ApproxSolution_rat N)
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℚ) :
    @Example_7_7.Z₂_bound ν.toPosReal N a.toReal (Matrix.ofRat A) =
    (Z₂_rat ν.val A a.aBar_fin : ℝ) := by
  unfold Example_7_7.Z₂_bound Z₂_rat
  simp only [ApproxSolution_rat.toReal_aBar_fin]
  rw [Rat.cast_mul, Rat.cast_ofNat]
  congr 1
  rw [Rat.cast_max]
  congr 1
  · exact finWeightedMatrixNorm_eq_rat ν A
  · simp only [one_div, mul_inv_rev, Rat.cast_mul, Rat.cast_inv, Rat.cast_ofNat,
    mul_eq_mul_right_iff, inv_inj, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
    rw [Rat.abs_eq_abs]
    rw [Rat.cast_abs]

/-- Z₁_bound on ℚ inputs = Z₁_rat -/
lemma Z₁_bound_eq_rat' (ν : PosRat) (a : ApproxSolution_rat N) :
    @Example_7_7.Z₁_bound ν.toPosReal N a.toReal =
    (Z₁_rat ν.val a.aBar_fin : ℝ) := by
  unfold Example_7_7.Z₁_bound Z₁_rat
  simp only [ApproxSolution_rat.toReal_aBar_fin, Example_7_7.ApproxSolution.toSeq]
  simp only [PosRat.toPosReal_val]
  rw [Rat.cast_mul, Rat.cast_div, Rat.cast_one]
  congr 1
  · rw [Rat.abs_eq_abs, Rat.cast_abs]
  · rw [Rat.cast_sum]
    congr 1
    ext k
    simp only [Rat.cast_mul, Rat.cast_pow]
    congr 1
    · simp only [finToSeq_rat]
      split_ifs with h
      · simp only [Rat.abs_eq_abs, Rat.cast_abs]
      · simp [Rat.abs_eq_abs]

/-- F_fin on ℚ inputs: the finite components of F(ā) = ā⋆ā - c -/
def F_fin_rat (lam0 : ℚ) (a : Fin (N+1) → ℚ) : Fin (N+1) → ℚ :=
  fun n => cauchyProduct_fin_rat a a n - paramSeq_rat lam0 n

/-- F_fin reflection: abstract F_fin equals F_fin_rat on ℚ inputs -/
lemma F_fin_eq_rat (ν : PosRat) (lam0 : ℚ) (a : ApproxSolution_rat N) (n : Fin (N+1)) :
    Example_7_7.F_fin (ν := ν.toPosReal) (lam0 : ℝ) a.toReal n =
    (F_fin_rat lam0 a.aBar_fin n : ℝ) := by
  unfold Example_7_7.F_fin Example_7_7.F F_fin_rat
  simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]
  simp only [Example_7_7.c, lpWeighted.mk_apply, Example_7_7.paramSeq]
  -- Convert sequences to ℚ form
  conv_lhs =>
    rw [show lpWeighted.toSeq (ν := ν.toPosReal) a.toReal.toL1 = fun k => (a.toSeq_rat k : ℝ) from funext (a.toReal_toL1_toSeq ν.toPosReal)]
  -- Now we have: (toSeq_rat ⋆ toSeq_rat) n - paramSeq n = cauchyProduct_fin_rat - paramSeq_rat
  rw [Rat.cast_sub]
  congr 1
  · -- CauchyProduct part
    rw [← cauchyProduct_fin_eq_rat]
    rfl
  · -- paramSeq part
    simp only [paramSeq_rat]
    rcases n with ⟨n, hn⟩
    match n with
    | 0 => rfl
    | 1 => simp only [Rat.cast_one]
    | n + 2 => simp only [Rat.cast_zero]

/-- Y₀_bound on ℚ inputs = Y₀_rat -/
lemma Y₀_bound_eq_rat' (ν : PosRat) (lam0 : ℚ) (a : ApproxSolution_rat N)
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℚ) :
    @Example_7_7.Y₀_bound ν.toPosReal N (lam0 : ℝ) a.toReal (Matrix.ofRat A) =
    (Y₀_rat ν.val A a.aBar_fin lam0 : ℝ) := by
  unfold Example_7_7.Y₀_bound Y₀_rat Y₀_finite_rat Y₀_tail_rat
  simp only [ApproxSolution_rat.toReal_aBar_fin, Example_7_7.ApproxSolution.toSeq]
  simp only [PosRat.toPosReal_val, Matrix.ofRat_apply]
  rw [Rat.cast_add]
  congr 1
  · -- Finite part: ∑ n, |∑ j, A n j * F_fin j| * ν^n
    rw [Rat.cast_sum]
    congr 1
    ext i
    rw [Rat.cast_mul, Rat.cast_pow]
    congr 1
    rw [Rat.abs_eq_abs, Rat.cast_abs, Rat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Rat.cast_mul]
    congr 1
    rw [F_fin_eq_rat ν lam0 a j]
    unfold F_component_rat F_fin_rat
    rfl
  · -- Tail part: (1/2|ā₀|) * ∑ n, (∑ k, |āₖ||āₙ₋ₖ|) * ν^n
    rw [Rat.cast_mul]
    congr 1
    · rw [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat]
      congr 1
      rw [Rat.abs_eq_abs, Rat.cast_abs]
    · rw [Rat.cast_sum]
      congr 1
      ext n
      rw [Rat.cast_mul, Rat.cast_pow]
      congr 1
      rw [Rat.cast_sum]
      congr 1
      ext k
      rw [Rat.cast_mul]
      congr 1 <;> rw [Rat.abs_eq_abs, Rat.cast_abs, finToSeq_rat_cast]

end ApproxSolutionRat
